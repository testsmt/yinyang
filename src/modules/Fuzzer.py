import random
import shutil
import os
import re
import signal

from pathlib import Path
from antlr4 import *

from src.modules.Solver import Solver, SolverQueryResult,  SolverResult
from src.modules.Statistic import Statistic

from config.config import crash_list, duplicate_list, ignore_list
from src.utils import random_string, plain, escape, in_list

from src.generators.TypeAwareOpMutation import TypeAwareOpMutation
from src.generators.SemanticFusion.SemanticFusion import SemanticFusion
from src.generators.TypeMutation import TypeMutation

class Fuzzer:

    def __init__(self, args):
        self.args = args
        self.currentseeds = ""
        self.runforever = True
        self.statistic = Statistic()
        self.generator = None


    def run(self):
        if (self.args.strategy == "opfuzz") or (self.args.strategy == "typfuzz"):
            seeds = self.args.PATH_TO_SEEDS
        elif (self.args.strategy == "fusion"):
            if len(self.args.PATH_TO_SEEDS) > 2:
                seeds = [(a, b) for a in self.args.PATH_TO_SEEDS for b in self.args.PATH_TO_SEEDS]
            elif len(self.args.PATH_TO_SEEDS) == 2:
                seeds = [(self.args.PATH_TO_SEEDS[0],self.args.PATH_TO_SEEDS[1])]
            else: assert(False)
        else: assert(False)

        while len(seeds) != 0:

            if (self.args.strategy == "opfuzz"):
                seed = seeds.pop(random.randrange(len(seeds)))
                self.statistic.seeds += 1
                self.currentseeds = Path(seed).stem
                self.generator = TypeAwareOpMutation([seed], self.args)
            elif (self.args.strategy == "fusion"):
                seed = seeds.pop(random.randrange(len(seeds)))
                seed1 = seed[0]
                seed2 = seed[1]
                self.statistic.seeds += 2
                self.currentseeds = Path(seed1).stem + "-" + Path(seed2).stem
                fusion_seeds = [seed1, seed2]
                self.generator = SemanticFusion(fusion_seeds, self.args)
            elif (self.args.strategy == "typfuzz"):
                seed = seeds.pop(random.randrange(len(seeds)))
                self.statistic.seeds += 1
                self.currentseeds = Path(seed).stem
                self.generator = TypeMutation([seed], self.args)
            else: assert(False)

            for _ in range(self.args.iterations):
                self.statistic.printbar()
                formula, success = self.generator.generate()
                if not success:
                    self.test(formula)
                    self.statistic.mutants += 1
                    break

                if not self.test(formula): break
                self.statistic.mutants += 1


    def create_testbook(self, formula):
        testbook = []
        if not self.args.keep_mutants:
            testcase = "%s/%s.smt2" % (self.args.scratchfolder, self.args.name)
        else:
            testcase = "%s/%s-%s-%s.smt2" % (self.args.scratchfolder,
                                             escape(self.currentseeds),
                                             self.args.name,random_string())
        with open(testcase, 'w') as testcase_writer:
            testcase_writer.write(formula.__str__())
        for cli in self.args.SOLVER_CLIS:
            if self.args.optfuzz != None:
                if not self.args.keep_mutants:
                    testcase = "%s/%s-%s" % (self.args.scratchfolder,
                                             plain(cli),
                                             self.args.name)
                else:
                    testcase = "%s/%s-%s-%s-%s.smt2" % (self.args.scratchfolder,
                                                        plain(cli),
                                                        escape(self.currentseeds),
                                                        self.args.name,random_string())
                with open(testcase, 'w') as testcase_writer:
                    testcase_writer.write(self.args.optfuzz.generate(cli) + formula.__str__())
            testbook.append((cli,testcase))
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
        if (self.args.oracle == "unknown"):
            return SolverResult(SolverQueryResult.UNKNOWN)
        elif (self.args.oracle == "sat"):
            return SolverResult(SolverQueryResult.SAT)
        elif (self.args.oracle == "unsat"):
            return SolverResult(SolverQueryResult.UNSAT)
        assert(False)


    def test(self, formula):
        """
        Tests the solvers with the formula returning "False" if the testing on
        formula should be stopped and "True" otherwise.
        """
        oracle = self.init_oracle()
        testbook = self.create_testbook(formula)
        reference = None

        for testitem in testbook:
            solver_cli, scratchfile = testitem[0], testitem[1]
            solver = Solver(solver_cli)
            stdout, stderr, exitcode = solver.solve(scratchfile, self.args.timeout, debug=self.args.diagnose)

            # (1) Detect crashes from a solver run including invalid models.
            if self.in_crash_list(stdout, stderr):

                # (2) Match against the duplicate list to avoid reporting duplicate bugs.
                if not self.in_duplicate_list(stdout, stderr):
                    self.statistic.crashes += 1
                    self.report(scratchfile, "crash", solver_cli, stdout, stderr, random_string())
                else:
                    self.statistic.duplicates += 1
                return False # stop testing
            else:
                # (3b) Check whether the exit code is nonzero.
                if exitcode == -signal.SIGSEGV or exitcode == 245: #segfault
                    self.statistic.crashes += 1
                    self.report(scratchfile, "segfault", solver_cli, stdout, stderr, random_string())
                    return False # stop testing

                elif exitcode == 137: #timeout
                    self.statistic.timeout += 1
                    continue # continue with next solver (4)

                elif exitcode == 127: #command not found
                    print("\nPlease check your solver command-line interfaces.")
                    continue # continue with next solver (4)

                # (3c) if there is no '^sat$' or '^unsat$' in the output
                elif not re.search("^unsat$", stdout, flags=re.MULTILINE) and \
                     not re.search("^sat$", stdout, flags=re.MULTILINE) and \
                     not re.search("^unknown$", stdout, flags=re.MULTILINE):
                    # (3a) Check whether the solver run produces errors, by checking
                    # the ignore list.
                    if self.in_ignore_list(stdout, stderr):
                        self.statistic.ignored += 1
                    continue # continue with next solver (4)
                else:
                    # (5) grep for '^sat$', '^unsat$', and '^unknown$' to produce
                    # the output (including '^unknown$' to also deal with incremental
                    # benchmarks) for comparing with the oracle (semantic fusion) or
                    # with other non-erroneous solver runs (opfuzz) for soundness bugs
                    result = self.grep_result(stdout)
                    if oracle.equals(SolverQueryResult.UNKNOWN):
                        oracle = result
                        reference = (solver_cli, scratchfile, stdout, stderr)

                    # Comparing with the oracle (semantic fusion) or with other
                    # non-erroneous solver runs (opfuzz) for soundness bugs.
                    if not oracle.equals(result):
                        self.statistic.soundness += 1
                        self.report(scratchfile, "incorrect", solver_cli, stdout, stderr, random_string())
                        if reference:
                            # Produce a diff bug report for soundness bugs in 
                            # the opfuzz case 
                            ref_cli = reference[0]
                            ref_stdout = reference[1]
                            ref_stderr = reference[2]
                            self.report_diff(scratchfile, "incorrect", 
                                             ref_cli, ref_stdout, ref_stderr, 
                                             solver_cli, stdout, stderr,
                                             random_string())
                        return False # stop testing
        return True

    def in_crash_list(self, stdout, stderr):
        return in_list(stdout,stderr,crash_list)

    def in_duplicate_list(self, stdout, stderr):
        return in_list(stdout,stderr,duplicate_list)

    def in_ignore_list(self,stdout, stderr):
        return in_list(stdout,stderr,ignore_list)

    def report(self, scratchfile, bugtype, cli, stdout, stderr, report_id):
        plain_cli = plain(cli)
        #format: <solver><{crash,wrong,invalid_model}><seed-name>.<random-string>.smt2
        report = "%s/%s-%s-%s-%s.smt2" %(self.args.bugsfolder, bugtype, plain_cli, escape(self.currentseeds), report_id)
        try: shutil.copy(scratchfile, report)
        except Exception as e:
            print(e)
            exit(0)
        logpath = "%s/%s-%s-%s-%s.output" %(self.args.bugsfolder, bugtype, plain_cli, escape(self.currentseeds), report_id)
        with open(logpath, 'w') as log:
            log.write("command: "+ cli+"\n")
            log.write("stderr:\n")
            log.write(stderr)
            log.write("stdout:\n")
            log.write(stdout)
        return report_id

    def report_diff(self, scratchfile, bugtype, 
                    ref_cli, ref_stdout, ref_stderr, 
                    sol_cli, sol_stdout, sol_stderr,
                    report_id):
        plain_cli = plain(sol_cli)
        #format: <solver><{crash,wrong,invalid_model}><seed-name>.<random-string>.smt2
        report = "%s/%s-%s-%s-%s.smt2" %(self.args.bugsfolder, bugtype, plain_cli, escape(self.currentseeds), report_id)
        try: shutil.copy(scratchfile, report)
        except Exception as e:
            print(e)
            exit(0)
        logpath = "%s/%s-%s-%s-%s.output" %(self.args.bugsfolder, bugtype, plain_cli, escape(self.currentseeds), report_id)
        with open(logpath, 'w') as log:
            log.write("*** REFERENCE \n")
            log.write("command: "+ ref_cli+"\n")
            log.write("stderr:\n")
            log.write(ref_stderr)
            log.write("stdout:\n")
            log.write(ref_stdout)
            log.write("\n\n*** INCORRECT \n")
            log.write("command: "+ sol_cli+"\n")
            log.write("stderr:\n")
            log.write(sol_stderr)
            log.write("stdout:\n")
            log.write(sol_stdout)
        return report_id


    def __del__(self):
        if not self.args.keep_mutants:
            for file in os.listdir(self.args.scratchfolder):
                if self.args.name in file:
                    os.remove(os.path.join(self.args.scratchfolder, file))
        self.statistic.printsum()
