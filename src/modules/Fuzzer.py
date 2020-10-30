import random
import shutil
import os

from pathlib import Path

from src.modules.Solver import SolverResultType, SolverResult, Solver
from src.modules.Statistic import Statistic

from src.utils import random_string, plain, escape

from src.generators.TypeAwareOpMutation import TypeAwareOpMutation
from src.generators.SemanticFusion.SemanticFusion import SemanticFusion

class Fuzzer:

    def __init__(self, args):
        self.args = args
        self.currentseeds = ""
        self.runforever = True
        self.statistic = Statistic()
        self.generator = None


    def run(self):
        seeds = self.args.PATH_TO_SEEDS
        if (self.args.strategy == "opfuzz" and len(seeds) == 1) or \
           (self.args.strategy == "fusion"  and len(seeds) == 2):
            self.runforever = False
        while True:
            if (self.args.strategy == "opfuzz"):
                seed = seeds[random.randrange(len(seeds))]
                self.statistic.seeds += 1
                self.currentseeds = Path(seed).stem
                self.generator = TypeAwareOpMutation([seed], self.args.opconfig)
            elif (self.args.strategy == "fusion"):
                seed1 = seeds[0]
                seed2 = seeds[1]
                self.statistic.seeds += 2
                self.currentseeds = Path(seed1).stem + "-" + Path(seed2).stem
                fusion_seeds = [seed1, seed2]
                self.generator = SemanticFusion(fusion_seeds, self.args.oracle, self.args.fusionfun)
            else: assert(False)
            for i in range(self.args.iterations):
                self.statistic.mutants += 1
                formula, success = self.generator.generate()

                if not success:
                    exit(0)

                if self.args.iterations% self.args.modulo:
                    continue

                valid, log = self.validate(formula)
                if not self.runforever and not valid:
                    print(log,flush=True)
                    exit(1)


            if not self.runforever:
                exit(0)

            if self.runforever:
                self.statistic.printbar()

    def validate(self, formula):
        ret = True
        log_str = ""
        if (self.args.oracle == "unknown"):
            oracle = SolverResult(SolverResultType.UNKNOWN)
        elif (self.args.oracle == "sat"):
            oracle = SolverResult(SolverResultType.SAT)
        elif (self.args.oracle == "unsat"):
            oracle = SolverResult(SolverResultType.UNSAT)
        else: assert(False)

        testbook = []
        for cli in self.args.SOLVER_CLIS:
            if not self.args.keep_mutants:
                testcase = "%s/%s.smt2" % (self.args.scratchfolder, self.args.name)
            else:
                testcase = "%s/%s-%s-%s-%s.smt2" % (self.args.scratchfolder,\
                                                    plain(cli),\
                                                    escape(self.currentseeds),\
                                                    self.args.name,\
                                                    random_string())
            with open(testcase, 'w') as testcase_writer:
                if self.args.optfuzz != None:
                    testcase_writer.write(self.args.optfuzz.generate(cli) + formula.__str__())
                else:
                    testcase_writer.write(formula.__str__())
            testbook.append((cli,testcase))

        reference = ("", "", "")
        for testitem in testbook:
            solver = Solver(testitem[0])
            result, output = solver.solve(testitem[1], self.args.timeout)
            # print("result", result)
            # print("output", output)
            if result.equals(SolverResultType.IGNORED):
                #ignored
                self.statistic.ignored += 1
            elif result.equals(SolverResultType.UNKNOWN):
                #unknown
                pass
            elif result.equals(SolverResultType.TIMEOUT):
                #timeout
                self.statistic.timeout += 1
            elif result.equals(SolverResultType.CRASH):
                #crash
                self.statistic.error += 1
                _,log_str = self.report(testitem[1], "crash", testitem[0], output, random_string())
                ret = False
            elif result.equals(SolverResultType.FAIL):
                print("\nPlease check your solver command-line interfaces.")
                exit(1)
            else:
                if oracle.equals(SolverResultType.UNKNOWN):
                    oracle = result
                    reference = (testitem[0], testitem[1], output)
                elif oracle.equals(result):
                    #correct
                    pass
                else:
                    #incorrect
                    self.statistic.soundness += 1
                    report_id, log_str = self.report(testitem[1], "incorrect", testitem[0], output, random_string(),oracle,result)
                    if reference !=  ("", "", ""):
                        _ ,log_str = self.report(reference[1], "incorrect", reference[0], reference[2], report_id, oracle, result)
                    ret = False

            if not self.args.keep_mutants:
                pass
                # print("testcase", testcase)
                # os.remove(testcase)

        return ret, log_str

    def report(self, trigger, bugtype, cli, output, report_id, reference=None, bad_result=None):
        plain_cli = plain(cli)
        #<solver><{crash,wrong,invalid_model}><seed-name>.<random-string>.smt2
        report = "%s/%s-%s-%s-%s.smt2" %(self.args.bugsfolder, bugtype, plain_cli, escape(self.currentseeds), report_id)
        try:
            shutil.copy(trigger, report)
        except Exception as e:
            print(e)
            exit(0)
        logpath = "%s/%s-%s-%s-%s.output" %(self.args.bugsfolder, bugtype, plain_cli, escape(self.currentseeds), report_id)
        log_str = ""
        if self.runforever:
            with open(logpath, 'w') as log:
                log.write("stderr:\n")
                log.write((output.stderr).decode("utf-8"))
                log.write("stdout:\n")
                log.write((output.stdout).decode("utf-8"))
        else:
            log_str = "\nBUG (%s): %s %s \n"  %(bugtype.upper(), cli, report)
            if bugtype == "incorrect":
                log_str +="*** REF results\n"
                log_str += reference.__str__()+"\n"
                log_str +="*** BAD results\n"
                log_str += bad_result.__str__()+"\n"
            else:
                log_str += output.stdout.decode("utf-8")
                log_str += "\n"
                log_str += output.stderr.decode("utf-8")

        return report_id, log_str

    def __del__(self):
        if not self.args.keep_mutants:
            os.remove("%s/%s.smt2" % (self.args.scratchfolder, self.args.name))
        if self.runforever:
            self.statistic.printsum()
