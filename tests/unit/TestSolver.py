# MIT License
#
# Copyright (c) [2020 - 2021] The yinyang authors
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
import shutil
import tempfile
import time
import unittest

from yinyang.src.core.Solver import Solver


def alive(pid):
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    # A killed process is a zombie until it is reaped; it can also be
    # reaped between os.kill and reading /proc, so a missing /proc entry
    # means the process is gone (on systems with /proc).
    try:
        with open("/proc/%d/stat" % pid) as f:
            return f.read().split(")")[-1].split()[0] != "Z"
    except OSError:
        return not os.path.isdir("/proc/self")


class SolverTestCase(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.mkdtemp()

    def tearDown(self):
        shutil.rmtree(self.dir)

    def script(self, name, body):
        path = os.path.join(self.dir, name)
        with open(path, "w") as f:
            f.write("#!/bin/sh\n" + body + "\n")
        os.chmod(path, 0o755)
        return path

    def test_output(self):
        solver = self.script("sat.sh", "echo sat; echo warning >&2; exit 3")
        self.assertEqual(Solver(solver).solve("x.smt2", 5),
                         ("sat\n", "warning\n", 3))

    def test_timeout_kills_wrapped_solver(self):
        # A wrapper script runs the "solver" (sleep) as its child. On
        # timeout the solver must be killed too, not only the wrapper.
        pidfile = os.path.join(self.dir, "pid")
        solver = self.script(
            "wrapper.sh", "sleep 60 &\necho $! > %s\nwait" % pidfile)
        start = time.time()
        _, _, returncode = Solver(solver).solve("x.smt2", 1)
        self.assertEqual(returncode, 137)
        self.assertLess(time.time() - start, 30)
        with open(pidfile) as f:
            pid = int(f.read())
        for _ in range(50):
            if not alive(pid):
                break
            time.sleep(0.1)
        self.assertFalse(alive(pid))


if __name__ == "__main__":
    unittest.main()
