import subprocess
import re

from enum import Enum
from config.config import crash_msgs, ignore_msgs

class SolverResultType(Enum):
    SAT = 0  # the solver reported SAT
    UNSAT = 1  # the solver reported UNSAT
    CRASH = 2  # the solver reported CRASH
    TIMEOUT = 3  # timeout occured
    FAIL = 4  # fail to open the file
    UNKNOWN = 5
    NO_OUTPUT = 6
    IGNORED = 7

def sr2str(sol_res):
    if sol_res == SolverResultType.SAT: return "sat"
    if sol_res == SolverResultType.UNSAT: return "unsat"
    if sol_res == SolverResultType.TIMEOUT: return "timeout"
    if sol_res == SolverResultType.UNKNOWN: return "unknown"
    if sol_res == SolverResultType.FAIL: return "fail"
    if sol_res == SolverResultType.NO_OUTPUT: return "no output"
    if sol_res == SolverResultType.IGNORED: return "ignored"


class SolverResult:

    def __init__(self, result=None):
        self.lst = []
        if result != None: self.lst.append(result)

    def append(self, result):
        self.lst.append(result)

    def equals(self, rhs):
        if type(rhs) == SolverResultType:
            return len(self.lst) == 1 and self.lst[0] == rhs
        elif type(rhs) == SolverResult:
            if len(self.lst) != len(rhs.lst): return False
            for index in range(0,len(self.lst)):
                if self.lst[index] != SolverResultType.UNKNOWN and \
                   rhs.lst[index] != SolverResultType.UNKNOWN and \
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



class Mockoutput:
    def __init__(self,stdout,stderr):
        self.stdout = stdout
        self.stderr = stderr

class Solver:
    def __init__ (self, cil):
        self.cil = cil

    def solve(self, file, timeout):
        try:
            output = subprocess.run(self.cil.split(" ") + [file], timeout=timeout, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        except subprocess.TimeoutExpired as te:
            if te.stdout != None and te.stderr != None:
                stdout = te.stdout.decode()
                stderr = te.stderr.decode()
            else:
                stdout = ""
                stderr = ""
            if self.warning_or_error(stdout,stderr):
                output = Mockoutput(te.stdout, te.stderr)
                return SolverResult(SolverResultType.CRASH), output
            else:
                return SolverResult(SolverResultType.TIMEOUT), "timeout"
        except KeyboardInterrupt:
            print("Accepted keyboard interrupt. Stop.")
            exit(0)
        except Exception as e:
            print("Exception rises when running solver:")
            print(e, '\n')
            exit(1)
            return SolverResult(SolverResultType.FAIL), "fail"

        stdout = output.stdout.decode()
        stderr = output.stderr.decode()
        print(stdout+"\n"+stderr,flush=True)

        if "Couldn't open file:" in stdout or "failed to open file" in stderr:
            return SolverResult(SolverResultType.FAIL), output
        elif self.ignored_error(stdout,stderr):
            return SolverResult(SolverResultType.IGNORED), output
        elif self.warning_or_error(stdout, stderr):
            return SolverResult(SolverResultType.CRASH), output
        elif not re.search("^unsat$", stdout, flags=re.MULTILINE) and \
             not re.search("^sat$", stdout, flags=re.MULTILINE) and \
             not re.search("^unknown$", stdout, flags=re.MULTILINE):
            return SolverResult(SolverResultType.CRASH), output
        else:
            result = SolverResult()
            for line in stdout.splitlines():
                if re.search("^unsat$", line, flags=re.MULTILINE):
                    result.append(SolverResultType.UNSAT)
                elif re.search("^sat$", line, flags=re.MULTILINE):
                    result.append(SolverResultType.SAT)
                elif re.search("^unknown$", line, flags=re.MULTILINE):
                    result.append(SolverResultType.UNKNOWN)
            return result, output


    def warning_or_error(self, stdout, stderr):
        stdstream = stdout + " " + stderr
        for err in crash_msgs:
            if err in stdstream: return True
        return False


    def ignored_error(self, stdout, stderr):
        stdstream = stdout + " " + stderr
        for err in ignore_msgs:
            if err in stdstream: return True
        return False
