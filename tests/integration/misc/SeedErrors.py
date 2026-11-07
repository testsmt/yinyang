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

# Checks that an error in yinyang on one seed (here a typechecker error on a
# seed with an undeclared symbol) does not stop the run: the seed is skipped
# and reported, and the other seeds are fuzzed.

import os
import shutil
import subprocess
import sys
import tempfile

python = sys.executable

GOOD = """(declare-fun x () Int)
(declare-fun y () Int)
(assert (> (+ x y) 1))
(check-sat)
"""

BAD = """(declare-fun x () Int)
(assert (> x y))
(check-sat)
"""


def fail(msg, cmd, output):
    print("[ERROR] " + msg)
    print(cmd)
    print(output)
    exit(1)


workdir = tempfile.mkdtemp()
try:
    seeds = os.path.join(workdir, "seeds")
    scratch = os.path.join(workdir, "scratch")
    logs = os.path.join(workdir, "logs")
    for folder in [seeds, scratch, logs]:
        os.makedirs(folder)
    for name, text in [("bad.smt2", BAD), ("good.smt2", GOOD)]:
        with open(os.path.join(seeds, name), "w") as f:
            f.write(text)
    solver = os.path.join(workdir, "sat.sh")
    with open(solver, "w") as f:
        f.write("#!/bin/sh\necho sat\n")
    os.chmod(solver, 0o755)

    cmd = "%s bin/typefuzz -k -i 2 -m 1 -s %s -b %s -l %s \"%s;%s\" %s" % (
        python, scratch, os.path.join(workdir, "bugs"), logs, solver,
        solver, seeds
    )
    out = subprocess.run(
        cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        universal_newlines=True
    )
    output = out.stdout
    if out.returncode != 0 or "Runtime error" in output:
        fail("typefuzz stopped on the bad seed", cmd, output)
    if "2 seeds processed, 1 valid, 1 invalid (1 failed in yinyang)" \
            not in output:
        fail("expected the bad seed to be reported", cmd, output)
    if not any(fn.startswith("good") for fn in os.listdir(scratch)):
        fail("expected mutants of the good seed", cmd, output)
    log = "".join(
        open(os.path.join(logs, fn)).read() for fn in os.listdir(logs)
    )
    if "error in yinyang while preparing: UnknownOperator" not in log \
            or "Traceback" not in log:
        fail("expected the error and its traceback in the log", cmd, log)
    print("SeedErrors: OK")
finally:
    shutil.rmtree(workdir)
