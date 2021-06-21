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
import random
import shutil
import datetime
import signal
import logging
from pathlib import Path
from logging.handlers import RotatingFileHandler

from src.modules.Statistic import Statistic
from src.modules.Solver import Solver, SolverQueryResult, SolverResult
from src.modules.exitcodes import OK_BUGS, OK_NOBUGS, ERR_EXHAUSTED_DISK

from src.parsing.parse import parse_file

from src.generators.TypeAwareOpMutation import TypeAwareOpMutation
from src.generators.SemanticFusion.SemanticFusion import SemanticFusion

from config.config import crash_list, duplicate_list, ignore_list
from src.utils import random_string, plain, escape, in_list


class bcolors:
    HEADER = "\033[95m"
    OKBLUE = "\033[94m"
    OKCYAN = "\033[96m"
    OKGREEN = "\033[92m"
    WARNING = "\033[91m"
    FAIL = "\033[91m"
    ENDC = "\033[0m"
    BOLD = "\033[1m"
    UNDERLINE = "\033[4m"


class Fuzzer:
    def __init__(self, args, strategy):
        self.args = args
        self.currentseeds = ""
        self.strategy = strategy
        self.runforever = True
        self.statistic = Statistic()
        self.generator = None
        self.old_time = time.time()
        self.start_time = time.time()
        self.first_status_bar_printed = False
        self.name = random_string()

        # Init logging
        fn = (
            datetime.datetime.now().strftime(
                self.strategy + "-%Y-%m-%d-%M:%S-%p")
            + "-"
            + str(self.name)
            + ".log"
        )
        log_fn = self.args.logfolder + "/" + fn

        logging.basicConfig(
            handlers=[
                RotatingFileHandler(
                    filename=log_fn, maxBytes=1024 * 1024, backupCount=5
                )
            ],
            format="%(asctime)s %(message)s",
            datefmt="[%Y/%m/%d %I:%M:%S %p]",
            level=logging.DEBUG,
        )
        if not self.args.quiet:
            console = logging.StreamHandler()
            formatter = logging.Formatter(
                "%(asctime)s %(message)s", datefmt="[%Y/%m/%d %I:%M:%S %p]"
            )
            console.setLevel(logging.INFO)
            console.setFormatter(formatter)
            logging.getLogger().addHandler(console)

    def admissible_seed_size(self, seed):
        """
        Checks if seed size is below file_size_limit.
        :returns: True if that is the case and False otherwise.
        """
        seed_size_in_bytes = Path(seed).stat().st_size
        if seed_size_in_bytes >= self.args.file_size_limit:
            return False
        return True

    def run(self):
        if self.strategy == "opfuzz":
            seeds = self.args.PATH_TO_SEEDS
        elif self.strategy == "yinyang":
            if len(self.args.PATH_TO_SEEDS) > 2:
                seeds = [
                    (a, b)
                    for a in self.args.PATH_TO_SEEDS
                    for b in self.args.PATH_TO_SEEDS
                ]
            elif len(self.args.PATH_TO_SEEDS) == 2:
                seeds = [
                    (self.args.PATH_TO_SEEDS[0], self.args.PATH_TO_SEEDS[1])
                ]
            else:
                assert False
        else:
            assert False

        num_targets = len(self.args.SOLVER_CLIS)
        logging.info(
            "Strategy: "
            + self.strategy
            + ", "
            + str(num_targets)
            + " testing targets, "
            + str(len(seeds))
            + " seeds"
        )

        while len(seeds) != 0:
            if self.strategy == "opfuzz":
                seed = seeds.pop(random.randrange(len(seeds)))

                logging.debug("Processing seed " + seed)
                self.statistic.total_seeds += 1

                if not self.admissible_seed_size(seed):
                    self.statistic.invalid_seeds += 1

                    logging.debug("Skip invalid seed: exceeds max file size")
                    continue

                self.currentseeds = Path(seed).stem
                script = parse_file(seed, silent=True)

                if not script:  # i.e. parsing was unsucessful
                    self.statistic.invalid_seeds += 1
                    logging.debug("Skipping invalid seed: error in parsing")
                    continue

                self.generator = TypeAwareOpMutation(script, self.args)

            elif self.strategy == "yinyang":
                seed = seeds.pop(random.randrange(len(seeds)))

                seed1 = seed[0]
                seed2 = seed[1]

                logging.debug("Processing seeds " + seed1 + " " + seed2)
                self.statistic.total_seeds += 2
                if not self.admissible_seed_size(
                    seed1
                ) or not self.admissible_seed_size(seed1):
                    self.statistic.invalid_seeds += 2
                    logging.debug("Skip invalid seed: exceeds max file size")
                    continue

                self.currentseeds = Path(seed1).stem + "-" + Path(seed2).stem
                script1 = parse_file(seed1, silent=True)
                script2 = parse_file(seed2, silent=True)

                if not script1 or not script2:  # i.e. parsing was unsucessful
                    self.statistic.invalid_seeds += 2
                    logging.debug("Skipping invalid seed: error in parsing")
                    continue

                self.generator = SemanticFusion(script1, script2, self.args)
            else:
                assert False

            logging.debug(
                "Attempting to generate "
                + str(self.args.iterations) + " mutants"
            )
            unsuccessful = 0
            for i in range(self.args.iterations):
                if (
                    not self.first_status_bar_printed
                    and time.time() - self.old_time >= 1
                ):
                    self.statistic.printbar(self.start_time)
                    self.old_time = time.time()
                    self.first_status_bar_printed = True

                if time.time() - self.old_time >= 5.0:
                    self.statistic.printbar(self.start_time)
                    self.old_time = time.time()

                formula, success, skip_seed = self.generator.generate()
                if not success:
                    self.statistic.unsuccessful_generations += 1
                    unsuccessful += 1
                    continue

                if not self.test(formula, i + 1):
                    break
                self.statistic.mutants += 1
                if skip_seed:
                    break

            successful = self.args.iterations - unsuccessful
            logging.debug(
                "Finished generations: "
                + str(successful)
                + " successful, "
                + str(unsuccessful)
                + " unsuccessful"
            )
        print("All seeds processed", flush=True)

        if not self.args.quiet:
            self.statistic.printsum()

        if self.statistic.crashes + self.statistic.soundness == 0:
            exit(OK_NOBUGS)
        exit(OK_BUGS)

    def create_testbook(self, formula):
        testbook = []
        #         if not self.args.keep_mutants:
        # testcase = "%s/%s.smt2" % (self.args.scratchfolder, self.args.name)
        # else:
        testcase = "%s/%s-%s-%s.smt2" % (
            self.args.scratchfolder,
            escape(self.currentseeds),
            self.name,
            random_string(),
        )
        with open(testcase, "w") as testcase_writer:
            testcase_writer.write(formula.__str__())
        for cli in self.args.SOLVER_CLIS:
            #             if self.args.optfuzz != None:
            # if not self.args.keep_mutants:
            # testcase = "%s/%s-%s" % (self.args.scratchfolder,
            # plain(cli),
            # self.args.name)
            # else:
            # testcase = "%s/%s-%s-%s-%s.smt2" % (self.args.scratchfolder,
            # plain(cli),
            # escape(self.currentseeds),
            # self.args.name,random_string())
            # with open(testcase, 'w') as testcase_writer:
            # testcase_writer.write(self.args.optfuzz.generate(cli) +
            # formula.__str__())
            testbook.append((cli, testcase))
        return testbook

    def grep_result(self, stdout):
        """
        Grep the result from the stdout of a solver.
        """
        result = SolverResult()
        for line in stdout.splitlines():
            if re.search("^unsat$", line, flags=re.MULTILINE):
                result.append(SolverQueryResult.UNSAT)
            elif re.search("^sat$", line, flags=re.MULTILINE):
                result.append(SolverQueryResult.SAT)
            elif re.search("^unknown$", line, flags=re.MULTILINE):
                result.append(SolverQueryResult.UNKNOWN)
        return result

    def init_oracle(self):
        """
        Initialize the oracle. For SemanticFusion the oracle is either sat or
        unsat. For TypeAwareOpMutation the oracle is unknown
        """
        if self.args.oracle == "unknown":
            return SolverResult(SolverQueryResult.UNKNOWN)
        elif self.args.oracle == "sat":
            return SolverResult(SolverQueryResult.SAT)
        elif self.args.oracle == "unsat":
            return SolverResult(SolverQueryResult.UNSAT)
        assert False

    def test(self, formula, i):
        """
        Tests the solvers with the formula returning "False" if the testing on
        formula should be stopped and "True" otherwise.
        """
        if self.strategy == "opfuzz":
            oracle = SolverResult(SolverQueryResult.UNKNOWN)
        else:
            oracle = self.init_oracle()

        testbook = self.create_testbook(formula)
        reference = None

        for testitem in testbook:
            solver_cli, scratchfile = testitem[0], testitem[1]
            solver = Solver(solver_cli)
            self.statistic.solver_calls += 1
            stdout, stderr, exitcode = solver.solve(
                scratchfile, self.args.timeout, debug=False
            )

            # (1) Detect crashes from a solver run including invalid models.
            if self.in_crash_list(stdout, stderr):

                # (2) Match against the duplicate list to avoid duplicate bugs.
                if not self.in_duplicate_list(stdout, stderr):
                    self.statistic.effective_calls += 1
                    self.statistic.crashes += 1
                    _, path = self.report(
                        scratchfile,
                        "crash",
                        solver_cli,
                        stdout,
                        stderr,
                        random_string(),
                    )
                    logging.debug("Crash! Stop testing on this seed.")
                    logging.info(
                        bcolors.BOLD
                        + bcolors.WARNING
                        + "Detected crash bug: "
                        + path
                        + bcolors.ENDC
                    )
                else:
                    self.statistic.duplicates += 1
                    logging.debug("Duplicate. Stop testing on this seed.")
                return False  # stop testing
            else:
                # Check whether the solver run produces errors, by checking
                # the ignore list.
                if self.in_ignore_list(stdout, stderr):
                    logging.debug(
                        "Invalid mutant:ignore_list. solver=" + str(solver_cli)
                    )
                    self.statistic.invalid_mutants += 1
                    continue  # continue with next solver (4)

                # (3b) Check whether the exit code is nonzero.
                if exitcode != 0:
                    # segfault
                    if exitcode == -signal.SIGSEGV or exitcode == 245:
                        self.statistic.effective_calls += 1
                        self.statistic.crashes += 1
                        _, path = self.report(
                            scratchfile,
                            "segfault",
                            solver_cli,
                            stdout,
                            stderr,
                            random_string(),
                        )
                        logging.debug(
                            str(i)
                            + "/"
                            + str(self.args.iterations)
                            + " Segfault! Stop testing on this seed."
                        )
                        logging.info(
                            bcolors.BOLD
                            + bcolors.WARNING
                            + "Detected segfault: "
                            + path
                            + bcolors.ENDC
                        )
                        return False  # stop testing

                    elif exitcode == 137:  # timeout
                        self.statistic.timeout += 1
                        logging.debug(
                            str(i)
                            + "/"
                            + str(self.args.iterations)
                            + " Solver timeout occured. sol="
                            + str(solver_cli)
                        )
                        continue  # continue with next solver (4)

                    elif exitcode == 127:  # command not found
                        continue  # continue with next solver (4)
                    # self.statistic.ignored+=1

                # (3c) if there is no '^sat$' or '^unsat$' in the output
                elif (
                    not re.search("^unsat$", stdout, flags=re.MULTILINE)
                    and not re.search("^sat$", stdout, flags=re.MULTILINE)
                    and not re.search("^unknown$", stdout, flags=re.MULTILINE)
                ):
                    self.statistic.ignored += 1
                    logging.debug(
                        str(i)
                        + "/"
                        + str(self.args.iterations)
                        + " Invalid mutant:no '^sat$' or '^unsat$' in output."
                    )
                else:
                    # grep for '^sat$', '^unsat$', and '^unknown$' to produce
                    # the output (including '^unknown$' to also deal with
                    # incremental benchmarks) for comparing with the oracle
                    # (semantic fusion) or with other non-erroneous solver runs
                    # (opfuzz) for soundness bugs
                    self.statistic.effective_calls += 1
                    result = self.grep_result(stdout)
                    if oracle.equals(SolverQueryResult.UNKNOWN):
                        oracle = result
                        reference = (solver_cli, scratchfile, stdout, stderr)

                    # Comparing with the oracle (semantic fusion) or with other
                    # non-erroneous solver runs (opfuzz) for soundness bugs.
                    if not oracle.equals(result):
                        self.statistic.soundness += 1
                        _, path = self.report(
                            scratchfile,
                            "incorrect",
                            solver_cli,
                            stdout,
                            stderr,
                            random_string(),
                        )
                        logging.debug(
                            str(i)
                            + "/"
                            + str(self.args.iterations)
                            + " Soundness bug! Stop testing on this seed."
                        )
                        logging.info(
                            bcolors.BOLD
                            + bcolors.WARNING
                            + "Detected soundness bug! "
                            + path
                            + bcolors.ENDC
                        )

                        if reference:
                            # Produce a diff bug report for soundness bugs in
                            # the opfuzz case
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
                                random_string(),
                            )
                        return False  # stop testing
        return True

    def in_crash_list(self, stdout, stderr):
        return in_list(stdout, stderr, crash_list)

    def in_duplicate_list(self, stdout, stderr):
        return in_list(stdout, stderr, duplicate_list)

    def in_ignore_list(self, stdout, stderr):
        return in_list(stdout, stderr, ignore_list)

    def report(self, scratchfile, bugtype, cli, stdout, stderr, report_id):
        plain_cli = plain(cli)
        # format: <solver><{crash,wrong,invalid_model}><seed>.<random-str>.smt2
        report = "%s/%s-%s-%s-%s.smt2" % (
            self.args.bugsfolder,
            bugtype,
            plain_cli,
            escape(self.currentseeds),
            report_id,
        )
        try:
            shutil.copy(scratchfile, report)
        except Exception:
            logging.error(
                "Could not copy scratchfile to bugfolder.\
                 Disk space seems exhausted."
            )
            exit(ERR_EXHAUSTED_DISK)
        logpath = "%s/%s-%s-%s-%s.output" % (
            self.args.bugsfolder,
            bugtype,
            plain_cli,
            escape(self.currentseeds),
            report_id,
        )
        with open(logpath, "w") as log:
            log.write("command: " + cli + "\n")
            log.write("stderr:\n")
            log.write(stderr)
            log.write("stdout:\n")
            log.write(stdout)
        return report_id, report

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
        report_id,
    ):
        plain_cli = plain(sol_cli)
        # format: <solver><{crash,wrong,invalid_model}><seed>.<random-str>.smt2
        report = "%s/%s-%s-%s-%s.smt2" % (
            self.args.bugsfolder,
            bugtype,
            plain_cli,
            escape(self.currentseeds),
            report_id,
        )
        try:
            shutil.copy(scratchfile, report)
        except Exception:
            logging.error("Could not copy scratchfile to bugfolder.\
                Disk space seems exhausted.")
            exit(ERR_EXHAUSTED_DISK)

        logpath = "%s/%s-%s-%s-%s.output" % (
            self.args.bugsfolder,
            bugtype,
            plain_cli,
            escape(self.currentseeds),
            report_id,
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
        return report_id, report

    def __del__(self):
        # remove files in scratchfolder
        for fn in os.listdir(self.args.scratchfolder):
            if self.name in fn:
                os.remove(os.path.join(self.args.scratchfolder, fn))
