# MIT License
#
# Copyright (c) [2020 - 2021] The yinyang authors
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

import os
import re
import time
import shutil
import random
import signal
import logging
import pathlib

from yinyang.src.core.Statistic import Statistic
from yinyang.src.core.Solver import Solver, SolverQueryResult, SolverResult

from yinyang.src.parsing.Parse import parse_file
from yinyang.src.parsing.Typechecker import typecheck
from yinyang.src.parsing.Logic import (
    parse_logic,
    infer_logic,
    divides_by_zero,
    logic_name,
    is_difference_logic,
)

from yinyang.src.mutators.TypeAwareOpMutation import TypeAwareOpMutation
from yinyang.src.mutators.SemanticFusion.SemanticFusion import SemanticFusion
from yinyang.src.mutators.GenTypeAwareMutation.Util import get_unique_subterms
from yinyang.src.mutators.GenTypeAwareMutation.GenTypeAwareMutation import (
    GenTypeAwareMutation
)


from yinyang.src.base.Utils import random_string, plain, escape
from yinyang.src.base.Exitcodes import OK_BUGS, OK_NOBUGS, ERR_EXHAUSTED_DISK

from yinyang.src.core.Logger import (
    init_logging,
    log_strategy_num_seeds,
    log_generation_attempt,
    log_finished_generations,
    log_crash_trigger,
    log_ignore_list_mutant,
    log_duplicate_trigger,
    log_segfault_trigger,
    log_signal_trigger,
    log_solver_timeout,
    log_soundness_trigger,
    log_invalid_mutant,
    log_skip_oversized_seed,
    log_skip_seed_mutator,
    log_skip_seed_test,
    log_skip_out_of_logic,
    log_skip_div_by_zero,
    log_seed_error,
)
from yinyang.src.core.FuzzerUtil import (
    get_seeds,
    grep_result,
    admissible_seed_size,
    in_crash_list,
    in_duplicate_list,
    in_ignore_list,
    crash_signal,
    init_oracle,
)

MAX_TIMEOUTS = 32


class Fuzzer:
    def __init__(self, args, strategy):
        self.args = args
        self.currentseeds = []
        self.strategy = strategy
        self.statistic = Statistic()
        self.generator = None
        self.old_time = time.time()
        self.start_time = time.time()
        self.first_status_bar_printed = False
        self.name = random_string()
        self.timeout_of_current_seed = 0
        self.header_comments = ""  # header comments to preserve in mutants
        self.seed_logic = None  # set-logic emitted for mutants of the seed
        self.logic_base = None  # features allowed by self.seed_logic
        self.current_logic = None  # set-logic emitted for the current mutant

        init_logging(strategy, self.args.quiet, self.name, args)
        if args.seed is not None:
            random.seed(args.seed)

    def extract_header_comments(self, seed_file):
        """
        Extract header comments (lines starting with ;) that appear before
        the first SMT-LIB command. These typically include EXPECT,
        COMMAND-LINE, etc.
        """
        header = []
        try:
            with open(seed_file, 'r') as f:
                for line in f:
                    stripped = line.strip()
                    if stripped.startswith(';'):
                        header.append(line.rstrip('\n'))
                    elif stripped and not stripped.startswith(';'):
                        # First non-comment, non-empty line - stop here
                        break
        except Exception:
            pass
        return '\n'.join(header) + ('\n' if header else '')

    def process_seed(self, seed):
        if not admissible_seed_size(seed, self.args):
            self.statistic.invalid_seeds += 1
            self.statistic.oversized_seeds += 1
            log_skip_oversized_seed(
                seed, pathlib.Path(seed).stat().st_size, self.args
            )
            return None, None

        self.currentseeds.append(pathlib.Path(seed).stem)
        # Extract header comments before parsing
        self.header_comments = self.extract_header_comments(seed)
        script, glob = parse_file(seed, silent=True)

        if not script:

            # Parsing was unsuccessful.
            self.statistic.invalid_seeds += 1
            logging.debug("Skipping invalid seed: error in parsing")
            return None, None

        return script, glob

    def get_script(self, seed):
        logging.debug("Processing seed " + seed)
        self.statistic.total_seeds += 1
        self.currentseeds = []
        return self.process_seed(seed)

    def get_script_pair(self, seed):
        seed1 = seed[0]
        seed2 = seed[1]
        logging.debug("Processing seeds " + seed1 + " " + seed2)
        self.statistic.total_seeds += 2
        self.currentseeds = []
        script1, glob1 = self.process_seed(seed1)
        script2, glob2 = self.process_seed(seed2)
        return script1, glob1, script2, glob2

    def max_timeouts_reached(self):
        if self.timeout_of_current_seed >= MAX_TIMEOUTS:
            return True
        return False  # stop testing if timeout limit is exceeded

    def init_mutator(self, seed):
        """
        Parse (and typecheck) the seed, or the pair of seeds for yinyang, and
        set up the mutator for it.

        :returns: False if the seed is invalid
        """
        if self.strategy == "typefuzz":
            script, glob = self.get_script(seed)
            if not script:
                return False
            self.init_logic([script])
            typecheck(script, glob)
            unique_expr = get_unique_subterms(script)
            self.mutator = GenTypeAwareMutation(
                script, self.args, unique_expr
            )

        elif self.strategy == "opfuzz":
            script, _ = self.get_script(seed)
            if not script:
                return False
            self.init_logic([script])
            self.mutator = TypeAwareOpMutation(script, self.args)

        elif self.strategy == "yinyang":
            script1, _, script2, _ = self.get_script_pair(seed)
            if not script1 or not script2:
                return False
            self.init_logic([script1, script2])
            self.mutator = SemanticFusion(script1, script2, self.args)

        else:
            assert False
        return True

    def run(self):
        """
        Realizes the main fuzzing loop. The procedure fetches seeds at random
        from the seed corpus (or a pair of seeds for yinyang), instantiates a
        mutator and then generates `self.args.iterations` many iterations per
        seed.
        """
        seeds, num_seeds = get_seeds(self.args, self.strategy)
        num_targets = len(self.args.SOLVER_CLIS)
        log_strategy_num_seeds(self.strategy, num_seeds, num_targets)

        for seed in seeds:
            # An error in yinyang on one seed (e.g. a typechecker or mutator
            # bug) must not stop the whole run: the seed is skipped.
            try:
                if not self.init_mutator(seed):
                    continue
            except Exception as e:
                n = 2 if self.strategy == "yinyang" else 1
                self.statistic.invalid_seeds += n
                self.statistic.failed_seeds += n
                log_seed_error(seed, "preparing", e)
                continue

            log_generation_attempt(self.args)

            unsuccessful_gens = 0
            successful_gens = 0
            self.timeout_of_current_seed = 0
            for i in range(self.args.iterations):
                self.print_stats()
                try:
                    mutant, success, skip_seed = self.mutator.mutate()
                except Exception as e:
                    self.statistic.mutator_errors += 1
                    log_seed_error(seed, "mutating", e)
                    break  # Continue to next seed.

                # Reason for unsuccessful generation: randomness in the
                # mutator to more efficiently generate mutants.
                if not success:
                    self.statistic.unsuccessful_generations += 1
                    unsuccessful_gens += 1
                    continue  # Go to next iteration.

                successful_gens += 1

                # Reason for mutator to skip a seed: no random components, i.e.
                # mutant would be the same for all  iterations and hence just
                # waste time.
                if skip_seed:
                    log_skip_seed_mutator(self.args, i)
                    break  # Continue to next seed.

                if self.args.div_by_zero == "skip" and \
                        divides_by_zero(mutant):
                    self.statistic.div_by_zero += 1
                    log_skip_div_by_zero(self.args, i)
                    continue  # Go to next iteration.

                logic, in_logic = self.mutant_logic(mutant)
                if not in_logic:
                    self.statistic.out_of_logic += 1
                    log_skip_out_of_logic(self.args, i, self.seed_logic)
                    continue  # Go to next iteration.
                self.current_logic = logic

                (mutate_further, scratchfile) = self.test(mutant, i + 1)
                if not mutate_further:  # Continue to next seed.
                    log_skip_seed_test(self.args, i)
                    break  # Continue to next seed.

                self.statistic.mutants += 1
                if not self.args.keep_mutants:
                    os.remove(scratchfile)

            log_finished_generations(successful_gens, unsuccessful_gens)
        self.terminate()

    def init_logic(self, scripts):
        """
        Determine the logic for the mutants of the given seed scripts from
        their set-logic commands (stored in script.logic by prepare_seed).

        Seeds without set-logic, and --logic-mode strip, give no set-logic.
        For logics that Logic.py does not understand (e.g. ALL) the logic is
        kept as is when all seeds agree and replaced by ALL otherwise.
        Difference logics are replaced by LIA/LRA as mutants rarely stay in
        difference form.
        """
        self.seed_logic, self.logic_base = None, None
        names = [script.logic for script in scripts]
        if self.args.logic_mode == "strip" or None in names:
            return
        bases = [parse_logic(name) for name in names]
        if None in bases:
            self.seed_logic = names[0] if len(set(names)) == 1 else "ALL"
            return

        # The features inferred from the seeds are added to the base, so
        # that imprecisions of infer_logic on the seeds themselves do not
        # cause widening or skipping.
        base = frozenset().union(
            *bases,
            *[infer_logic(script, self.args.div_by_zero)
              for script in scripts]
        )
        self.logic_base = base
        if len(set(names)) == 1 and not is_difference_logic(names[0]):
            self.seed_logic = names[0]
        else:
            self.seed_logic = logic_name(base)

    def mutant_logic(self, mutant):
        """
        Determine the set-logic for a mutant. If the mutant uses features
        outside of the seed's logic, the logic is widened to include them
        (--logic-mode widen) or the mutant is rejected (--logic-mode skip).

        :returns: (logic, in_logic) where logic is the logic name or None
                  for no set-logic, and in_logic is False if the mutant
                  should be skipped.
        """
        if self.logic_base is None:
            return self.seed_logic, True
        needed = infer_logic(mutant, self.args.div_by_zero)
        if needed <= self.logic_base:
            return self.seed_logic, True
        if self.args.logic_mode == "skip":
            return None, False
        return logic_name(self.logic_base | needed), True

    def script_str(self, script):
        """
        Print a mutant, with the set-logic command for the current mutant
        inserted after the leading set-option commands (some solvers reject
        set-option after set-logic).
        """
        if self.current_logic is None:
            return script.__str__()
        cmds = [cmd.__str__() for cmd in script.commands]
        i = 0
        while i < len(cmds) and cmds[i].lstrip().startswith("(set-option"):
            i += 1
        cmds.insert(i, "(set-logic " + self.current_logic + ")")
        return "\n".join(cmds)

    def create_testbook(self, script):
        """
        Generate a "testbook" for script and solver configs.

        script:     parsed SMT-LIB script
        :returns:   list containing with cli and testcases pairs
        """
        testbook = []
        testcase = "%s/%s-%s-%s.smt2" % (
            self.args.scratchfolder,
            escape("-".join(self.currentseeds)),
            self.name,
            random_string(),
        )
        with open(testcase, "w") as testcase_writer:
            # Prepend header comments if they exist
            if self.header_comments:
                testcase_writer.write(self.header_comments)
            testcase_writer.write(self.script_str(script))

        for cli in self.args.SOLVER_CLIS:
            testbook.append((cli, testcase))
        return testbook

    def test(self, script, iteration):
        """
        Tests the solvers on the provided script. Checks for crashes, segfaults
        invalid models and soundness issues, ignores duplicates. Stores bug
        triggers in ./bugs along with .output files for bug reproduction.

        script:     parsed SMT-LIB script
        iteration:  number of current iteration (used for logging)
        :returns:   False if the testing on the script should be stopped
                    and True otherwise.
        """

        # For differential testing (opfuzz), the oracle is set to "unknown" and
        # gets overwritten by the result of the first solver call. For
        # metamorphic testing (yinyang) the oracle is pre-set by the cmd line.
        if self.strategy in ["opfuzz", "typefuzz"]:
            oracle = SolverResult(SolverQueryResult.UNKNOWN)
        else:
            oracle = init_oracle(self.args)

        testbook = self.create_testbook(script)
        reference = None
        scratchfile = None
        for testitem in testbook:
            solver_cli, scratchfile = testitem[0], testitem[1]
            solver = Solver(solver_cli)
            self.statistic.solver_calls += 1
            stdout, stderr, exitcode = solver.solve(
                scratchfile, self.args.timeout
            )

            if self.max_timeouts_reached():
                return (False, scratchfile)

            # Match stdout and stderr against the crash list
            # (see yinyang/config/Config.py:27) which contains various
            # crash messages such as assertion errors, check failure,
            # invalid models, etc.
            if in_crash_list(stdout, stderr):

                # Match stdout and stderr against the duplicate list
                # (see yinyang/config/Config.py:51) to prevent catching
                # duplicate bug triggers.
                if not in_duplicate_list(stdout, stderr):
                    self.statistic.effective_calls += 1
                    self.statistic.crashes += 1
                    path = self.report(
                        script, "crash", solver_cli, stdout, stderr
                    )
                    log_crash_trigger(path)
                else:
                    self.statistic.duplicates += 1
                    log_duplicate_trigger()
                return (False, scratchfile)  # Stop testing.
            else:

                # Check whether the solver crashed with a signal such as
                # SIGSEGV or SIGABRT. This is checked before the ignore list:
                # a solver that prints an error and then crashes is still
                # buggy.
                sig = crash_signal(exitcode)
                if sig is not None:
                    self.statistic.effective_calls += 1
                    self.statistic.crashes += 1
                    if sig == signal.SIGSEGV:
                        path = self.report(
                            script, "segfault", solver_cli, stdout, stderr
                        )
                        log_segfault_trigger(self.args, path, iteration)
                    else:
                        path = self.report(
                            script, "crash", solver_cli, stdout, stderr
                        )
                        log_signal_trigger(
                            self.args, path, iteration, sig.name
                        )
                    return (False, scratchfile)  # Stop testing.

                # Check whether the solver call produced errors, e.g, related
                # to its parser, options, type-checker etc., by matching stdout
                # and stderr against the ignore list
                # (see yinyang/config/Config.py:54).
                if in_ignore_list(stdout, stderr):
                    log_ignore_list_mutant(solver_cli)
                    self.statistic.invalid_mutants += 1
                    continue  # Continue to the next solver.

                if exitcode != 0:

                    # Check whether the solver timed out.
                    if exitcode == 137:
                        self.statistic.timeout += 1
                        self.timeout_of_current_seed += 1
                        log_solver_timeout(self.args, solver_cli, iteration)
                        continue  # Continue to the next solver.

                    # Check whether a "command not found" error occurred.
                    elif exitcode == 127:
                        continue  # Continue to the next solver.

                # Check if the stdout contains a valid solver query result,
                # i.e., contains lines with 'sat', 'unsat' or 'unknown'.
                if (
                    not re.search("^unsat$", stdout, flags=re.MULTILINE)
                    and not re.search("^sat$", stdout, flags=re.MULTILINE)
                    and not re.search("^unknown$", stdout, flags=re.MULTILINE)
                ):
                    self.statistic.invalid_mutants += 1
                    log_invalid_mutant(self.args, iteration)
                    continue  # Continue to the next solver.

                else:

                    # Grep for '^sat$', '^unsat$', and '^unknown$' to produce
                    # the output (including '^unknown$' to also deal with
                    # incremental benchmarks) for comparing with the oracle
                    # (yinyang) or with other non-erroneous solver runs
                    # (opfuzz) for soundness bugs.
                    self.statistic.effective_calls += 1
                    result = grep_result(stdout)
                    if oracle.equals(SolverQueryResult.UNKNOWN):

                        # For differential testing (opfuzz), the first solver
                        # is set as the reference, its result to be the oracle.
                        oracle = result
                        reference = (solver_cli, stdout, stderr)

                    # Comparing with the oracle (yinyang) or with other
                    # non-erroneous solver runs (opfuzz) for soundness bugs.
                    if not oracle.equals(result):
                        self.statistic.soundness += 1

                        if reference:

                            # Produce a bug report for soundness bugs
                            # containing a diff with the reference solver
                            # (opfuzz).
                            ref_cli = reference[0]
                            ref_stdout = reference[1]
                            ref_stderr = reference[2]
                            path = self.report_diff(
                                script,
                                "incorrect",
                                ref_cli,
                                ref_stdout,
                                ref_stderr,
                                solver_cli,
                                stdout,
                                stderr,
                            )
                        else:

                            # Produce a bug report if the query result differs
                            # from the pre-set oracle (yinyang).
                            path = self.report(
                                script, "incorrect", solver_cli,
                                stdout, stderr
                            )

                        log_soundness_trigger(self.args, iteration, path)
                        return (False, scratchfile)  # Stop testing.
        return (True, scratchfile)  # Continue to next seed.

    def write_bug_trigger(self, script, bugtype, cli):
        """
        Write the bug trigger to the bug folder. The .smt2 file and the
        .output file written by the caller share one name:
        <bugtype>-<solver>-<seeds>-<random-str>.{smt2,output}

        :returns:   (path of the .smt2 file, path of the .output file)
        """
        base = "%s/%s-%s-%s-%s" % (
            self.args.bugsfolder,
            bugtype,
            plain(cli),
            escape("-".join(self.currentseeds)),
            random_string(),
        )
        report = base + ".smt2"
        try:
            with open(report, "w") as report_writer:
                report_writer.write(self.script_str(script))
        except Exception:
            logging.error("error: couldn't copy scratchfile to bugfolder.")
            exit(ERR_EXHAUSTED_DISK)
        return report, base + ".output"

    def report(self, script, bugtype, cli, stdout, stderr):
        report, logpath = self.write_bug_trigger(script, bugtype, cli)
        with open(logpath, "w") as log:
            log.write("command: " + cli + "\n")
            log.write("stderr:\n")
            log.write(stderr)
            log.write("stdout:\n")
            log.write(stdout)
        return report

    def report_diff(
        self,
        script,
        bugtype,
        ref_cli,
        ref_stdout,
        ref_stderr,
        sol_cli,
        sol_stdout,
        sol_stderr,
    ):
        report, logpath = self.write_bug_trigger(script, bugtype, sol_cli)
        with open(logpath, "w") as log:
            log.write("*** REFERENCE \n")
            log.write("command: " + ref_cli + "\n")
            log.write("stderr:\n")
            log.write(ref_stderr)
            log.write("stdout:\n")
            log.write(ref_stdout)
            log.write("\n\n*** INCORRECT \n")
            log.write("command: " + sol_cli + "\n")
            log.write("stderr:\n")
            log.write(sol_stderr)
            log.write("stdout:\n")
            log.write(sol_stdout)
        return report

    def print_stats(self):
        if not self.first_status_bar_printed\
           and time.time() - self.old_time >= 1:
            self.statistic.printbar(self.start_time)
            self.old_time = time.time()
            self.first_status_bar_printed = True

        if time.time() - self.old_time >= 2.0:
            self.statistic.printbar(self.start_time)
            self.old_time = time.time()

    def terminate(self):
        print("All seeds processed", flush=True)
        if not self.args.quiet:
            self.statistic.printsum()
        if self.statistic.crashes + self.statistic.soundness == 0:
            exit(OK_NOBUGS)
        exit(OK_BUGS)

    def __del__(self):
        if not self.args.keep_mutants:
            for fn in os.listdir(self.args.scratchfolder):
                if self.name in fn:
                    os.remove(os.path.join(self.args.scratchfolder, fn))
