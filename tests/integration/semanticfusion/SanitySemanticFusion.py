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
import sys
import subprocess

N = 2
python = sys.executable


def call_fuzzer(first_config, fn, opts):
    cmd = python + " bin/yinyang "\
        + '"' + first_config + '" ' + opts + " " + fn
    output = subprocess.getoutput(cmd)
    print(output)
    soundness_issues = 0
    crash_issues = 0
    for line in output.split("\n"):
        if "soundness" in line:
            soundness_issues += 1
        if "crash" in line or "invalid model" in line:
            crash_issues += 1

    return soundness_issues, crash_issues, cmd


def get_z3():
    z3_link = (
        "https://github.com/Z3Prover/z3/releases/download/z3-4.8.6/"
        + "z3-4.8.6-x64-ubuntu-16.04.zip"
    )
    subprocess.getoutput("wget " + z3_link)
    subprocess.getoutput("unzip z3-4.8.6-x64-ubuntu-16.04.zip")
    return os.path.abspath("z3-4.8.6-x64-ubuntu-16.04/bin/z3")


def get_cvc4():
    cvc4_link = (
        "http://cvc4.cs.stanford.edu/downloads/builds/"
        + "x86_64-linux-opt/cvc4-1.6-x86_64-linux-opt"
    )
    subprocess.getoutput("wget " + cvc4_link)
    subprocess.getoutput("chmod +x cvc4-1.6-x86_64-linux-opt")
    return os.path.abspath("cvc4-1.6-x86_64-linux-opt")


def cleanup():
    subprocess.getoutput("rm -rf z3*")
    subprocess.getoutput("rm -rf cvc4*")


cleanup()
#
# 1. download z3 and cvc4
#
print("Downloading solvers...")
print("Get z3")
z3 = get_z3()

print("Get cvc4")
cvc4 = get_cvc4()

# 2. ensure no soundness bugs in Semantic Fusion.
#
first_config = z3
fn = "tests/integration/semanticfusion/intersection-example-simple.proof-node75884.smt2 tests/integration/semanticfusion/water_tank-node5020.smt2"  # noqa: E501
opts = "-o unsat -s fusion"

print("Trying to sanitize unsat fusion...")
bug_catched = False
for _ in range(N):
    soundness_issues, crash_issues, cmd = call_fuzzer(first_config, fn, opts)
    if soundness_issues != 0 or crash_issues != 0:
        bug_catched = True
        break

if bug_catched:
    print("[ERROR] Unexpected bugs found.")
    print(cmd)
    exit(1)

first_config = z3
fn = "tests/integration/semanticfusion/37315_issue-1694.smt2 tests/integration/semanticfusion/37315_issue-1694.smt2"  # noqa: E501
opts = "-o sat -s fusion"

print("Trying to sanitize sat fusion...")
bug_catched = False
for _ in range(N):
    soundness_issues, crash_issues, cmd = call_fuzzer(first_config, fn, opts)
    if soundness_issues != 0 or crash_issues != 0:
        bug_catched = True
        break

if bug_catched:
    print("[ERROR] Unexpected bugs found.")
    print(cmd)
    exit(1)


# 3. retrigger bug with unsat fusion
#
print("Trying to retrigger bug with unsat fusion...")
first_config = cvc4 + " --strings-exp -q"
fn = "tests/integration/semanticfusion/gIxXB_cvc4_bug_incorrect_script1.smt2 tests/integration/semanticfusion/gIxXB_cvc4_bug_incorrect_script2.smt2"  # noqa: E501
opts = "-o unsat -s fusion"

for _ in range(1000):
    soundness_issues, crash_issues, cmd = call_fuzzer(first_config, fn, opts)
    if soundness_issues != 0:
        bug_catched = True
        break

if not bug_catched:
    print("[ERROR] Bug not found by unsat fusion.")
    print(cmd)
    exit(1)

# 4. retrigger bug with unsat fusion
#
print("Trying to retrigger bug with sat fusion...")
first_config = z3
fn = "tests/integration/semanticfusion/5jby0_z3_bug_incorrect_script1.smt2 tests/integration/semanticfusion/5jby0_z3_bug_incorrect_script2.smt2"  # noqa: E501
opts = "-o sat -s fusion"

for _ in range(1000):
    soundness_issues, crash_issues, cmd = call_fuzzer(first_config, fn, opts)
    if soundness_issues != 0:
        bug_catched = True
        break

if not bug_catched:
    print("[ERROR] Bug not found by sat fusion.")
    print(cmd)
    exit(1)


cleanup()

print("[SUCCESS] All sanitizer passed.")
