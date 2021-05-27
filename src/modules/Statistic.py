import time
import logging

class Statistic:

    def __init__(self):
        # print("Yin-Yang is running:")
        self.starttime = time.time()
        self.seeds = 0
        self.mutants = 0
        self.crashes= 0
        self.soundness = 0
        self.duplicates = 0
        self.timeout = 0
        self.ignored = 0
        self.solver_calls = 0
        self.effective_calls = 0

    def printbar(self, start_time):
        total_time = time.time() - start_time
        bar="Performed %d solver calls (%d calls/s, eff: %d, %d mutants/s)" %(self.solver_calls, self.solver_calls / total_time, float(self.effective_calls // self.solver_calls),self.mutants/total_time)
        logging.warning(bar)

    def printsum(self):
        summary = """

Summary:
Passed time: %ds
Generated mutants: %d
Used seeds: %d
Crash issues: %d
Soundness issues: %d
Duplicate issues: %d
Timeout cases: %d
Ignored issues: %d
""" \
        % (time.time()-self.starttime, self.mutants, self.seeds,  self.crashes, self.soundness, self.duplicates, self.timeout, self.ignored)
        # print(summary, end="\n", flush=True)
