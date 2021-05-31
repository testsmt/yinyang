import time
import logging

class Statistic:

    def __init__(self):
        self.starttime = time.time()
        self.total_seeds = 0
        self.invalid_seeds = 0
        self.total_generations = 0
        self.unsuccessful_generations = 0
        self.mutants = 0
        self.invalid_mutants = 0
        self.crashes= 0
        self.soundness = 0
        self.duplicates = 0
        self.timeout = 0
        self.solver_calls = 0
        self.effective_calls = 0

    def printbar(self, start_time):
        total_time = time.time() - start_time
        if self.solver_calls != 0:
            eff = round((float(self.effective_calls) / float(self.solver_calls))*100, 1)
            eff_str = str(eff) + "%"
        else:
            eff_str = "NaN"

        solver_calls_per_sec = round(float(self.solver_calls) / float(total_time), 1)
        solver_calls_per_sec_str= round(float(self.solver_calls) / float(total_time), 1)

        mutants_per_sec = round(float(self.mutants) / float(total_time), 1)
        mutants_per_sec_str = str(mutants_per_sec)
        bar="Performed %d solver calls (%s calls/s, eff: %s, %s mutants/s)"\
             %(self.solver_calls, solver_calls_per_sec_str, eff_str, mutants_per_sec_str)
        logging.info(bar)

    def printsum(self):
        valid_seeds = self.total_seeds - self.invalid_seeds
        num_bugs = self.crashes + self.soundness
        summary = "\b\b\r%d seeds processed, %d valid, %d invalid \n%d bug triggers found"\
                   %(self.total_seeds, valid_seeds, self.invalid_seeds, num_bugs)
        print(summary)
