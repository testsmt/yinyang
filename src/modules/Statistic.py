import time

class Statistic:
    
    def __init__(self):
    
        self.starttime = time.time()
        self.seeds = 0
        self.mutants = 0
        self.error = 0
        self.soundness = 0
        self.timeout = 0
        self.ignored = 0

    def printbar(self):
        bar = "Yin-Yang is running: [passed time=%ds, passed tests=%d, used seeds=%d, errors/crashes=%d, soundness issues=%d, timeout cases=%d, ignored issues=%d]" \
              % (time.time()-self.starttime, self.mutants, self.seeds, self.error, self.soundness, self.timeout, self.ignored)
        print(bar, end="\r", flush=True)
    
    def printsum(self):
        summary = """
        
Summary:
Passed time=%ds
Passed tests=%d, 
Used seeds=%d, 
Errors/crashes=%d, 
Soundness issues=%d, 
Timeout cases=%d, 
Ignored issues=%d
""" \
        % (time.time()-self.starttime, self.mutants, self.seeds,  self.error, self.soundness, self.timeout, self.ignored)
        print(summary, end="\n", flush=True)