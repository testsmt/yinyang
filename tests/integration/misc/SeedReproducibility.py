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

# Checks that --seed makes typefuzz, opfuzz and yinyang reproducible: two runs
# with the same seed generate the same mutants (also with different Python
# hash seeds), and a run with another seed generates different ones. Runs
# with the same seed use different file names, so they do not overwrite each
# other's mutants in a shared scratch folder.

import os
import shutil
import subprocess
import sys
import tempfile

python = sys.executable

SEED = """(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (> (+ x y) (- z 1)))
(assert (or (< x 3) (>= (* 2 y) z)))
(assert (distinct x y z))
(check-sat)
"""

ITERATIONS = 10


def run(tool, opts, workdir, scratch, hashseed):
    os.makedirs(scratch, exist_ok=True)
    logs = os.path.join(workdir, "logs")
    os.makedirs(logs, exist_ok=True)
    solver = os.path.join(workdir, "solver.sh")
    seed = os.path.join(workdir, "seed.smt2")
    seeds = seed + " " + seed if tool == "yinyang" else seed
    cmd = "%s bin/%s %s -k -s %s -l %s -i %d \"%s;%s\" %s" % (
        python, tool, opts, scratch, logs, ITERATIONS, solver, solver, seeds
    )
    env = dict(os.environ, PYTHONHASHSEED=str(hashseed))
    out = subprocess.run(
        cmd, shell=True, env=env, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, universal_newlines=True
    )
    if out.returncode != 0:
        print(cmd)
        print(out.stdout)
        exit(1)
    return cmd


def mutants(scratch):
    contents = []
    for fn in os.listdir(scratch):
        with open(os.path.join(scratch, fn)) as f:
            contents.append(f.read())
    return sorted(contents)


def check(tool, extra_opts):
    workdir = tempfile.mkdtemp()
    try:
        with open(os.path.join(workdir, "seed.smt2"), "w") as f:
            f.write(SEED)
        solver = os.path.join(workdir, "solver.sh")
        with open(solver, "w") as f:
            f.write("#!/bin/sh\necho sat\n")
        os.chmod(solver, 0o755)

        def scratch(name):
            return os.path.join(workdir, name)

        cmd = run(tool, extra_opts + " --seed 1", workdir, scratch("a"), 1)
        run(tool, extra_opts + " --seed 1", workdir, scratch("b"), 2)
        run(tool, extra_opts + " --seed 2", workdir, scratch("c"), 1)
        a, b, c = (mutants(scratch(n)) for n in "abc")
        if not a:
            print("[ERROR] %s generated no mutants" % tool)
            print(cmd)
            exit(1)
        if a != b:
            print("[ERROR] %s --seed 1 is not reproducible" % tool)
            print(cmd)
            exit(1)
        if a == c:
            print("[ERROR] %s --seed 1 and --seed 2 give the same mutants"
                  % tool)
            print(cmd)
            exit(1)

        # Same seed and the same scratch folder: no file is overwritten.
        run(tool, extra_opts + " --seed 1", workdir, scratch("a"), 1)
        if len(os.listdir(scratch("a"))) != 2 * len(a):
            print("[ERROR] %s runs with the same --seed overwrite mutants"
                  % tool)
            print(cmd)
            exit(1)
        print("%s: %d mutants, reproducible with --seed" % (tool, len(a)))
    finally:
        shutil.rmtree(workdir)


check("opfuzz", "-m 1")
check("typefuzz", "-m 1")
check("yinyang", "-o sat")
