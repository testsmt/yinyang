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
import subprocess
import sys

N = 300
python = sys.executable


def call_fuzzer(first_config, second_config, fn, opts):
    cmd = (
        python
        + " bin/opfuzz "
        + '"'
        + first_config
        + ";"
        + second_config
        + '" '
        + opts
        + " "
        + fn
    )
    output = subprocess.getoutput(cmd)
    soundness_issues = 0
    crash_issues = 0
    for line in output.split("\n"):
        if "Detected soundness bug" in line:
            soundness_issues += 1
        if "Detected crash bug" in line or "Detected segfault":
            crash_issues += 1

    return soundness_issues, crash_issues, cmd


def get_cvc4():
    cvc4_link = (
        "https://github.com/CVC4/CVC4/releases/download/1.7/"
        + "cvc4-1.7-x86_64-linux-opt"
    )
    subprocess.getoutput("wget " + cvc4_link)
    subprocess.getoutput("chmod +x cvc4-1.7-x86_64-linux-opt")
    return os.path.abspath("cvc4-1.7-x86_64-linux-opt")


def get_z3():
    z3_link = (
        "https://github.com/Z3Prover/z3/releases/download/z3-4.8.6/"
        + "z3-4.8.6-x64-ubuntu-16.04.zip"
    )
    subprocess.getoutput("wget " + z3_link)
    subprocess.getoutput("unzip z3-4.8.6-x64-ubuntu-16.04.zip")
    return os.path.abspath("z3-4.8.6-x64-ubuntu-16.04/bin/z3")


def cleanup():
    subprocess.getoutput("rm -rf cvc4*")
    subprocess.getoutput("rm -rf z3*")


cleanup()
#
# 1. download z3 and cvc4
#
print("Downloading solvers...")
print("Get cvc4")
cvc4 = get_cvc4()

print("Get z3")
z3 = get_z3()

# 2. check whether bugs can be retriggered
#
first_config = cvc4 + " -q"
second_config = cvc4 + " --sygus-inference -q"
fn = "tests/integration/opfuzz/cvc4_wrong_3564_hidden.smt2"
opts = "-i 1 -m 1"

print("Trying to retrigger soundness bug...")
bug_catched = False
for _ in range(N):
    soundness_issues, crash_issues, cmd = call_fuzzer(
        first_config, second_config, fn, opts
    )
    if soundness_issues == 1:
        bug_catched = True
        break

if not bug_catched:
    print("[ERROR] Soundness bug could not be reproduced.")
    print(cmd)
    exit(1)

first_config = z3 + " model_validate=true"
second_config = cvc4 + " --incremental --produce-models -q"
fn = "tests/integration/opfuzz/z3_invmodel_3118_hidden.smt2"
opts = "-i 1 -m 1"

print("Trying to retrigger invalid model bug...")
bug_catched = False
for _ in range(N):
    soundness_issues, crash_issues, cmd = call_fuzzer(
        first_config, second_config, fn, opts
    )
    if crash_issues != 0:
        bug_catched = True
        break

if not bug_catched:
    print("[ERROR] Invalid model bug could not be reproduced.")
    print(cmd)
    exit(1)

first_config = z3 + " model_validate=true"
second_config = cvc4 + " --incremental --produce-models -q"
fn = "tests/integration/opfuzz/z3-segfault-3549.smt2"
opts = "-i 1 -m 1"

print("Trying to retrigger segfault...")
bug_catched = False
for _ in range(N):
    soundness_issues, crash_issues, cmd = call_fuzzer(
        first_config, second_config, fn, opts
    )
    if crash_issues != 0:
        bug_catched = True
        break

if not bug_catched:
    print("[ERROR] Crash bug could not be reproduced.")
    print(cmd)
    exit(1)

cleanup()

print("[SUCCESS] All bugs retriggered.")
