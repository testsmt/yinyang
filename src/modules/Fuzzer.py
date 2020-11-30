import random
import shutil
import os

from pathlib import Path
from antlr4 import *

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

        if (self.args.strategy == "opfuzz"):
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
            else: assert(False)
            
            for _ in range(self.args.iterations):
                self.statistic.printbar()
                formula, success = self.generator.generate()
                if not success:
                    print(formula.__str__())
                    exit(0)
                if not self.validate(formula): break
                self.statistic.mutants += 1

    def validate(self, formula):

        if (self.args.oracle == "unknown"):
            oracle = SolverResult(SolverResultType.UNKNOWN)
        elif (self.args.oracle == "sat"):
            oracle = SolverResult(SolverResultType.SAT)
        elif (self.args.oracle == "unsat"):
            oracle = SolverResult(SolverResultType.UNSAT)
        else: assert(False)

        testbook = []
        if not self.args.keep_mutants:
            testcase = "%s/%s.smt2" % (self.args.scratchfolder, self.args.name)
        else:
            testcase = "%s/%s-%s-%s.smt2" % (self.args.scratchfolder,escape(self.currentseeds),self.args.name,random_string())
        with open(testcase, 'w') as testcase_writer:
            testcase_writer.write(formula.__str__())
        for cli in self.args.SOLVER_CLIS:
            if self.args.optfuzz != None:
                if not self.args.keep_mutants:
                    testcase = "%s/%s-%s" % (self.args.scratchfolder, plain(cli), self.args.name)
                else:
                    testcase = "%s/%s-%s-%s-%s.smt2" % (self.args.scratchfolder,plain(cli),escape(self.currentseeds),self.args.name,random_string())
                with open(testcase, 'w') as testcase_writer:
                    testcase_writer.write(self.args.optfuzz.generate(cli) + formula.__str__())
            testbook.append((cli,testcase))
        
        reference = ("", "", "")
        for testitem in testbook:
            solver = Solver(testitem[0])
            result, output = solver.solve(testitem[1], self.args.timeout)

            if result.equals(SolverResultType.IGNORED):
                #ignored
                self.statistic.ignored += 1
                return False
            elif result.equals(SolverResultType.UNKNOWN):
                #unknown
                pass
            elif result.equals(SolverResultType.TIMEOUT):
                #timeout
                self.statistic.timeout += 1
            elif result.equals(SolverResultType.CRASH):
                #crash
                self.statistic.error += 1
                self.report(testitem[1], "crash", testitem[0], output, random_string())
                return False
            elif result.equals(SolverResultType.FAIL):
                print("\nPlease check your solver command-line interfaces.")
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
                    if reference != ("", "", ""):
                        if self.args.optfuzz != None:
                            report_id = self.report(testitem[1], "incorrect", testitem[0], output, random_string())
                            self.report(reference[1], "incorrect", reference[0], reference[2], report_id) 
                        else:
                            self.reportdiff(testitem[1], "incorrect", (testitem[0], reference[0]), (output, reference[2]), random_string())
                    else:
                        self.report(testitem[1], "incorrect", testitem[0], output, random_string())
                    return False

        return True

    def report(self, trigger, bugtype, cli, output, report_id):
        plain_cli = plain(cli)
        #<solver><{crash,wrong,invalid_model}><seed-name>.<random-string>.smt2
        report = "%s/%s-%s-%s-%s.smt2" %(self.args.bugsfolder, bugtype, plain_cli, escape(self.currentseeds), report_id)
        try: shutil.copy(trigger, report)
        except Exception as e: 
            print(e)
            exit(0)
        logpath = "%s/%s-%s-%s-%s.output" %(self.args.bugsfolder, bugtype, plain_cli, escape(self.currentseeds), report_id)
        with open(logpath, 'w') as log:
            log.write("command: "+ plain_cli+"\n")
            log.write("stderr:\n")
            log.write((output.stderr).decode("utf-8"))
            log.write("stdout:\n")
            log.write((output.stdout).decode("utf-8"))
        return report_id
    
    def reportdiff(self, trigger, bugtype, cli_pair, output_pair, report_id):
        plain_cli = plain(cli_pair[0]) + "-" + plain(cli_pair[1])
        report = "%s/%s-%s-%s-%s.smt2" %(self.args.bugsfolder, bugtype, plain_cli, escape(self.currentseeds), report_id)
        try: shutil.copy(trigger, report)
        except Exception as e: 
            print(e)
            exit(0)
        logpath = "%s/%s-%s-%s-%s.output" %(self.args.bugsfolder, bugtype, plain_cli, escape(self.currentseeds), report_id)
        with open(logpath, 'w') as log:
            log.write("command: "+plain(cli_pair[0])+"\n")
            log.write("stderr:\n")
            log.write((output_pair[0].stderr).decode("utf-8"))
            log.write("stdout:\n")
            log.write((output_pair[0].stdout).decode("utf-8"))
            log.write("*************************\n")
            log.write("command: "+plain(cli_pair[1])+"\n")
            log.write("stderr:\n")
            log.write((output_pair[1].stderr).decode("utf-8")+"\n")
            log.write("stdout:\n")
            log.write((output_pair[1].stdout).decode("utf-8")+"\n")
        return report_id

    def __del__(self):
        if not self.args.keep_mutants:
            for file in os.listdir(self.args.scratchfolder):
                if self.args.name in file:
                    os.remove(os.path.join(self.args.scratchfolder, file))
        self.statistic.printsum()
