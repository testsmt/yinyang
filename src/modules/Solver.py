import subprocess
import re

from enum import Enum

class SolverQueryResult(Enum):
    """
    Enum to store the result of a single solver query through "(check-sat)" query.
    """
    SAT = 0         # solver query reports SAT
    UNSAT = 1       # solver query reports UNSAT
    UNKNOWN = 2     # solver query reports UNKNOWN

def sr2str(sol_res):
    if sol_res == SolverQueryResult.SAT: return "sat"
    if sol_res == SolverQueryResult.UNSAT: return "unsat"
    if sol_res == SolverQueryResult.UNKNOWN: return "unknown"

class SolverResult:
    """
    Class to store the result of multiple solver querys throught "(check-sat)" query.
    :lst a list of multiple "SolverQueryResult" items
    """
    def __init__(self, result=None):
        self.lst = []
        if result != None: self.lst.append(result)

    def append(self, result):
        self.lst.append(result)

    def equals(self, rhs):
        if type(rhs) == SolverQueryResult:
            return len(self.lst) == 1 and self.lst[0] == rhs
        elif type(rhs) == SolverResult:
            if len(self.lst) != len(rhs.lst): return False
            for index in range(0,len(self.lst)):
                if self.lst[index] != SolverQueryResult.UNKNOWN and \
                   rhs.lst[index] != SolverQueryResult.UNKNOWN and \
                   self.lst[index] != rhs.lst[index]:
                   return False
            return True
        else:
            return False

    def __str__(self):
        s = sr2str(self.lst[0])
        for res in self.lst[1:]:
           s+= "\n" + sr2str(res)
        return s


class Solver:
    def __init__ (self, cil):
        self.cil = cil

    def solve(self, file, timeout, debug=False):
        try:
            cmd = list(filter(None, self.cil.split(" "))) + [file]
            if debug:
                print("cmd: "+" ".join(cmd), flush=True)
            output = subprocess.run(cmd, timeout=timeout,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE,
                                    shell=False)
        except subprocess.TimeoutExpired as te:
            if te.stdout != None and te.stderr != None:
                stdout = te.stdout.decode()
                stderr = te.stderr.decode()
            else:
                stdout = ""
                stderr = ""
            return stdout, stderr, 137
        # except KeyboardInterrupt:
            # exit(0)
        except ValueError as e:
            print("Subprocess bug.")
            stdout = ""
            stderr = ""
            return stdout, stderr, 0
        except Exception as e:
            print("Exception rises when running solver:")
            print(e, '\n')
            exit(1)


        stdout = output.stdout.decode()
        stderr = output.stderr.decode()
        returncode = output.returncode

        if debug:
            print("output: "+ stdout+"\n"+stderr)

        return stdout, stderr, returncode
