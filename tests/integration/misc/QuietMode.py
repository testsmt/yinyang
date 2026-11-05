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

# Checks that typefuzz, opfuzz and yinyang still fuzz with -q: mutants are
# tested, bugs are written to the bug folder and the exit code tells whether
# bugs were found, while no statistics are printed.

import os
import shutil
import subprocess
import sys
import tempfile

python = sys.executable

OK_NOBUGS = 0
OK_BUGS = 10

SEED = """(declare-fun x () Int)
(declare-fun y () Int)
(assert (> (+ x y) 1))
(assert (distinct x y))
(check-sat)
"""


def run(tool, solver, workdir):
    scratch = os.path.join(workdir, "scratch")
    bugs = os.path.join(workdir, "bugs")
    logs = os.path.join(workdir, "logs")
    for folder in [scratch, bugs, logs]:
        shutil.rmtree(folder, ignore_errors=True)
        os.makedirs(folder)
    seed = os.path.join(workdir, "seed.smt2")
    seeds = seed + " " + seed if tool == "yinyang" else seed
    opts = "-o sat" if tool == "yinyang" else "-m 1"
    cmd = "%s bin/%s -q -k -i 2 %s -s %s -b %s -l %s \"%s;%s\" %s" % (
        python, tool, opts, scratch, bugs, logs, solver, solver, seeds
    )
    out = subprocess.run(
        cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        universal_newlines=True
    )
    return out.returncode, out.stdout, os.listdir(scratch), \
        os.listdir(bugs), cmd


def fail(msg, cmd, output):
    print("[ERROR] " + msg)
    print(cmd)
    print(output)
    exit(1)


def check(tool, workdir):
    sat = os.path.join(workdir, "sat.sh")
    crash = os.path.join(workdir, "crash.sh")

    rc, out, mutants, bugs, cmd = run(tool, sat, workdir)
    if rc != OK_NOBUGS or not mutants or bugs:
        fail("%s -q: expected exit code %d, mutants and no bugs, got exit"
             " code %d, %d mutants, %d bug files"
             % (tool, OK_NOBUGS, rc, len(mutants), len(bugs)), cmd, out)

    rc, out, mutants, bugs, cmd = run(tool, crash, workdir)
    if rc != OK_BUGS or not bugs:
        fail("%s -q: expected exit code %d and bug files, got exit code %d"
             " and %d bug files" % (tool, OK_BUGS, rc, len(bugs)), cmd, out)
    if "Detected" in out or "bug triggers found" in out:
        fail("%s -q printed statistics or bug reports" % tool, cmd, out)
    print("%s -q: OK" % tool)


workdir = tempfile.mkdtemp()
try:
    with open(os.path.join(workdir, "seed.smt2"), "w") as f:
        f.write(SEED)
    for name, body in [("sat.sh", "echo sat"),
                       ("crash.sh", "kill -SEGV $$")]:
        path = os.path.join(workdir, name)
        with open(path, "w") as f:
            f.write("#!/bin/sh\n" + body + "\n")
        os.chmod(path, 0o755)
    for tool in ["typefuzz", "opfuzz", "yinyang"]:
        check(tool, workdir)
finally:
    shutil.rmtree(workdir)
