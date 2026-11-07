# MIT License
#
# Copyright (c) [2020 - 2020] The yinyang authors
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
import signal
import subprocess
from enum import Enum

from yinyang.src.base.Exitcodes import ERR_USAGE


class SolverQueryResult(Enum):
    """
    Enum storing the result of a single solver check-sat query.
    """

    SAT = 0  # solver query returns "sat"
    UNSAT = 1  # solver query returns "unsat"
    UNKNOWN = 2  # solver query reports "unknown"


def sr2str(sol_res):
    if sol_res == SolverQueryResult.SAT:
        return "sat"
    if sol_res == SolverQueryResult.UNSAT:
        return "unsat"
    if sol_res == SolverQueryResult.UNKNOWN:
        return "unknown"


class SolverResult:
    """
    Class to store the result of multiple solver check-sat queries.
    :lst a list of multiple "SolverQueryResult" items
    """

    def __init__(self, result=None):
        self.lst = []
        if result:
            self.lst.append(result)

    def append(self, result):
        self.lst.append(result)

    def equals(self, rhs):
        if isinstance(rhs, SolverQueryResult):
            return len(self.lst) == 1 and self.lst[0] == rhs
        elif isinstance(rhs, SolverResult):
            if len(self.lst) != len(rhs.lst):
                return False
            for index in range(0, len(self.lst)):
                if (
                    self.lst[index] != SolverQueryResult.UNKNOWN
                    and rhs.lst[index] != SolverQueryResult.UNKNOWN
                    and self.lst[index] != rhs.lst[index]
                ):
                    return False
            return True
        else:
            return False

    def __str__(self):
        s = sr2str(self.lst[0])
        for res in self.lst[1:]:
            s += "\n" + sr2str(res)
        return s


class Solver:
    def __init__(self, cil):
        self.cil = cil

    def solve(self, file, timeout, debug=False):
        """
        Run the solver on file. The solver runs in a process group of its
        own, which is killed on timeout: solvers started by a wrapper script
        must not keep running after the wrapper is killed.
        """
        try:
            cmd = list(filter(None, self.cil.split(" "))) + [file]
            if debug:
                print("cmd: " + " ".join(cmd), flush=True)
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                shell=False,
                start_new_session=True,
            )

        except ValueError:
            stdout = ""
            stderr = ""
            return stdout, stderr, 0

        except FileNotFoundError:
            print('error: solver "' + cmd[0] + '" not found', flush=True)
            exit(ERR_USAGE)

        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            kill_process_group(process)
            stdout, stderr = process.communicate()
            if stdout and stderr:
                return stdout.decode(), stderr.decode(), 137
            return "", "", 137
        except BaseException:
            kill_process_group(process)
            process.wait()
            raise

        stdout = stdout.decode()
        stderr = stderr.decode()
        returncode = process.returncode

        if debug:
            print("output: " + stdout + "\n" + stderr)

        return stdout, stderr, returncode


def kill_process_group(process):
    """
    Kill the process and all processes in its process group (see
    start_new_session in Solver.solve).
    """
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except (AttributeError, ProcessLookupError, PermissionError):
        # No process groups (Windows), or the group is already gone.
        process.kill()
