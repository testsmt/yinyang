import time

class Statistic:
    
    def __init__(self):
        print("Yin-Yang is running:")
        self.starttime = time.time()
        self.seeds = 0
        self.mutants = 0
        self.error = 0
        self.soundness = 0
        self.timeout = 0
        self.ignored = 0

    def printbar(self):
        bar = "[time:%ds, #mutant:%d, #seed:%d, #crash:%d, #unsound:%d, #timeout:%d, #ignored:%d]" \
              % (time.time()-self.starttime, self.mutants, self.seeds, self.error, self.soundness, self.timeout, self.ignored)
        print(bar, end="\r", flush=True)
    
    def printsum(self):
        summary = """
        
Summary:
Passed time: %ds
Generated mutants: %d
Used seeds: %d
Crash issues: %d
Unsound issues: %d
Timeout cases: %d
Ignored issues: %d
""" \
        % (time.time()-self.starttime, self.mutants, self.seeds,  self.error, self.soundness, self.timeout, self.ignored)
        print(summary, end="\n", flush=True)