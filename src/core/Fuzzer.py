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
import copy
import time
import shutil
import random
import signal
import logging
import pathlib

from src.core.Statistic import Statistic
from src.core.Solver import Solver, SolverQueryResult, SolverResult

from src.parsing.Parse import parse_file
from src.parsing.Typechecker import typecheck

from src.mutators.TypeAwareOpMutation import TypeAwareOpMutation
from src.mutators.SemanticFusion.SemanticFusion import SemanticFusion
from src.mutators.GenTypeAwareMutation.Util import get_unique_subterms
from src.mutators.GenTypeAwareMutation.GenTypeAwareMutation import (
    GenTypeAwareMutation
)


from src.base.Utils import random_string, plain, escape
from src.base.Exitcodes import OK_BUGS, OK_NOBUGS, ERR_EXHAUSTED_DISK

from src.core.Logger import (
    init_logging,
    log_strategy_num_seeds,
    log_generation_attempt,
    log_finished_generations,
    log_crash_trigger,
    log_ignore_list_mutant,
    log_duplicate_trigger,
    log_segfault_trigger,
    log_solver_timeout,
    log_soundness_trigger,
    log_invalid_mutant,
)
from src.core.FuzzerUtil import (
    get_seeds,
    grep_result,
    admissible_seed_size,
    in_crash_list,
    in_duplicate_list,
    in_ignore_list,
    init_oracle,
)

MAX_TIMEOUTS = 32


class Fuzzer:
    def __init__(self, args, strategy):
        self.args = args
        self.currentseeds = ""
        self.strategy = strategy
        self.statistic = Statistic()
        self.generator = None
        self.old_time = time.time()
        self.start_time = time.time()
        self.first_status_bar_printed = False
        self.name = random_string()
        self.timeout_of_current_seed = 0

        init_logging(strategy, self.args.quiet, self.name, args)

    def process_seed(self, seed):
        if not admissible_seed_size(seed, self.args):
            self.statistic.invalid_seeds += 1
            logging.debug("Skip invalid seed: exceeds max file size")
            return None, None

        self.currentseeds = pathlib.Path(seed).stem
        script, glob = parse_file(seed, silent=True)

        if not script:

            # Parsing was unsuccessful.
            self.statistic.invalid_seeds += 1
            logging.debug("Skipping invalid seed: error in parsing")
            return None, None

        return script, glob

    def get_script(self, seeds):
        seed = seeds.pop(random.randrange(len(seeds)))
        logging.debug("Processing seed " + seed)
        self.statistic.total_seeds += 1
        return self.process_seed(seed)

    def get_script_pair(self, seeds):
        seed = seeds.pop(random.randrange(len(seeds)))
        seed1 = seed[0]
        seed2 = seed[1]
        logging.debug("Processing seeds " + seed1 + " " + seed2)
        self.statistic.total_seeds += 2
        script1, glob1 = self.process_seed(seed1)
        script2, glob2 = self.process_seed(seed2)
        return script1, glob1, script2, glob2

    def max_timeouts_reached(self):
        if self.timeout_of_current_seed >= MAX_TIMEOUTS:
            return True
        return False  # stop testing if timeout limit is exceeded

    def run(self):
        """
        Realizes the main fuzzing loop. The procedure fetches seeds at random
        from the seed corpus (or a pair of seeds for yinyang), instantiates a
        mutator and then generates `self.args.iterations` many iterations per
        seed.
        """
        seeds = get_seeds(self.args, self.strategy)
        log_strategy_num_seeds(self.strategy, seeds, self.args.SOLVER_CLIS)

        while len(seeds) != 0:
            if self.strategy == "typefuzz":
                script, glob = self.get_script(seeds)
                if not script:
                    continue

                typecheck(script, glob)
                script_cp = copy.deepcopy(script)
                unique_expr = get_unique_subterms(script_cp)
                self.mutator = GenTypeAwareMutation(
                    script, self.args, unique_expr
                )

            elif self.strategy == "opfuzz":
                script, _ = self.get_script(seeds)
                if not script:
                    continue
                self.mutator = TypeAwareOpMutation(script, self.args)

            elif self.strategy == "yinyang":
                script1, _, script2, _ = self.get_script_pair(seeds)
                if not script1 or not script2:
                    continue
                self.mutator = SemanticFusion(script1, script2, self.args)

            else:
                assert False

            log_generation_attempt(self.args)

            unsuccessful_gens = 0
            for i in range(self.args.iterations):
                self.print_stats()
                mutant, success, skip_seed = self.mutator.mutate()

                # Reason for unsuccessful generation: randomness in the
                # mutator to more efficiently generate mutants.
                if not success:
                    self.statistic.unsuccessful_generations += 1
                    unsuccessful_gens += 1
                    continue  # Go to next iteration.

                # Reason for mutator to skip a seed: no random components, i.e.
                # mutant would be the same for all  iterations and hence just
                # waste time.
                if skip_seed:
                    break  # Continue to next seed.

                if not self.test(mutant, i + 1):  # Continue to next seed.
                    break

                self.statistic.mutants += 1

            log_finished_generations(self.args, unsuccessful_gens)
        self.terminate()

    def create_testbook(self, script):
        """
        Generate a "testbook" for script and solver configs.

        script:     parsed SMT-LIB script
        :returns:   list containing with cli and testcases pairs
        """
        testbook = []
        testcase = "%s/%s-%s-%s.smt2" % (
            self.args.scratchfolder,
            escape(self.currentseeds),
            self.name,
            random_string(),
        )
        with open(testcase, "w") as testcase_writer:
            testcase_writer.write(script.__str__())

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

        for testitem in testbook:
            solver_cli, scratchfile = testitem[0], testitem[1]
            solver = Solver(solver_cli)
            self.statistic.solver_calls += 1
            stdout, stderr, exitcode = solver.solve(
                scratchfile, self.args.timeout
            )

            if self.max_timeouts_reached():
                return False

            # Match stdout and stderr against the crash list
            # (see config/Config.py:27) which contains various crash messages
            # such as assertion errors, check failure, invalid models, etc.
            if in_crash_list(stdout, stderr):

                # Match stdout and stderr against the duplicate list
                # (see config/Config.py:51) to prevent catching duplicate bug
                # triggers.
                if not in_duplicate_list(stdout, stderr):
                    self.statistic.effective_calls += 1
                    self.statistic.crashes += 1
                    path = self.report(
                        scratchfile, "crash", solver_cli, stdout, stderr
                    )
                    log_crash_trigger(path)
                else:
                    self.statistic.duplicates += 1
                    log_duplicate_trigger()
                return False  # Stop testing.
            else:

                # Check whether the solver call produced errors, e.g, related
                # to its parser, options, type-checker etc., by matching stdout
                # and stderr against the ignore list (see config/Config.py:54).
                if in_ignore_list(stdout, stderr):
                    log_ignore_list_mutant(solver_cli)
                    self.statistic.invalid_mutants += 1
                    continue  # Continue to the next solver.

                if exitcode != 0:

                    # Check whether the solver crashed with a segfault.
                    if exitcode == -signal.SIGSEGV or exitcode == 245:
                        self.statistic.effective_calls += 1
                        self.statistic.crashes += 1
                        path = self.report(
                            scratchfile, "segfault", solver_cli, stdout, stderr
                        )
                        log_segfault_trigger(self.args, path, iteration)
                        return False  # Stop testing.

                    # Check whether the solver timed out.
                    elif exitcode == 137:
                        self.statistic.timeout += 1
                        self.timeout_of_current_seed += 1
                        log_solver_timeout(self.args, solver_cli, iteration)
                        continue  # Continue to the next solver.

                    # Check whether a "command not found" error occurred.
                    elif exitcode == 127:
                        continue  # Continue to the next solver.

                # Check if the stdout contains a valid solver query result,
                # i.e., contains lines with 'sat', 'unsat' or 'unknown'.
                elif (
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
                        reference = (solver_cli, scratchfile, stdout, stderr)

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
                                scratchfile,
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
                                scratchfile, "incorrect", solver_cli,
                                stdout, stderr
                            )

                        log_soundness_trigger(self.args, iteration, path)
                        return False  # Stop testing.
        return True  # Continue to next seed.

    def report(self, scratchfile, bugtype, cli, stdout, stderr):
        plain_cli = plain(cli)
        # format: <solver><{crash,wrong,invalid_model}><seed>.<random-str>.smt2
        report = "%s/%s-%s-%s-%s.smt2" % (
            self.args.bugsfolder,
            bugtype,
            plain_cli,
            escape(self.currentseeds),
            random_string(),
        )
        try:
            shutil.copy(scratchfile, report)
        except Exception:
            logging.error("error: couldn't copy scratchfile to bugfolder.")
            exit(ERR_EXHAUSTED_DISK)
        logpath = "%s/%s-%s-%s-%s.output" % (
            self.args.bugsfolder,
            bugtype,
            plain_cli,
            escape(self.currentseeds),
            random_string(),
        )
        with open(logpath, "w") as log:
            log.write("command: " + cli + "\n")
            log.write("stderr:\n")
            log.write(stderr)
            log.write("stdout:\n")
            log.write(stdout)
        return report

    def report_diff(
        self,
        scratchfile,
        bugtype,
        ref_cli,
        ref_stdout,
        ref_stderr,
        sol_cli,
        sol_stdout,
        sol_stderr,
    ):
        plain_cli = plain(sol_cli)
        # format: <solver><{crash,wrong,invalid_model}><seed>.<random-str>.smt2
        report = "%s/%s-%s-%s-%s.smt2" % (
            self.args.bugsfolder,
            bugtype,
            plain_cli,
            escape(self.currentseeds),
            random_string(),
        )
        try:
            shutil.copy(scratchfile, report)
        except Exception:
            logging.error("error: couldn't copy scratchfile to bugfolder.")
            exit(ERR_EXHAUSTED_DISK)

        logpath = "%s/%s-%s-%s-%s.output" % (
            self.args.bugsfolder,
            bugtype,
            plain_cli,
            escape(self.currentseeds),
            random_string(),
        )
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
        for fn in os.listdir(self.args.scratchfolder):
            if self.name in fn:
                os.remove(os.path.join(self.args.scratchfolder, fn))
