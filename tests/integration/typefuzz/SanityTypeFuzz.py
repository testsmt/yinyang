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

python = sys.executable


def call_fuzzer(first_config, second_config, fn, opts):
    cmd = (
        "timeout -s 9 1 "
        + python
        + " bin/typefuzz "
        + '"'
        + first_config
        + ";"
        + second_config
        + '" '
        + opts
        + " "
        + fn
    )
    print(cmd)
    output = subprocess.getoutput(cmd)
    print(output)
    soundness_issues = 0
    crash_issues = 0
    for line in output.split("\n"):
        if "Detected soundness bug" in line:
            soundness_issues += 1
        if "Detected crash bug" in line or "Detected segfault":
            crash_issues += 1

    return soundness_issues, crash_issues, cmd


def get_cvc4_1_8():
    cvc4_link = (
        "https://github.com/CVC4/CVC4/releases/download/1.8/"
        + "cvc4-1.8-x86_64-linux-opt"
    )
    subprocess.getoutput("wget " + cvc4_link)
    subprocess.getoutput("chmod +x cvc4-1.8-x86_64-linux-opt")
    return os.path.abspath("cvc4-1.8-x86_64-linux-opt")


def get_z3_4_8_6():
    z3_link = (
        "https://github.com/Z3Prover/z3/releases/download/z3-4.8.6/"
        + "z3-4.8.6-x64-ubuntu-16.04.zip"
    )
    subprocess.getoutput("wget " + z3_link)
    subprocess.getoutput("unzip z3-4.8.6-x64-ubuntu-16.04.zip")
    return os.path.abspath("z3-4.8.6-x64-ubuntu-16.04/bin/z3")


def execute(cmd):
    print(cmd, flush=True)
    out = os.system(cmd)


def get_z3_trunk(commit_id):
    execute("git clone https://github.com/Z3Prover/z3.git " + commit_id)
    cmd = ("cd " + commit_id + ";"
           + "git checkout " + commit_id + ";"
           + "./configure;"
           + "cd build;"
           + "make -j 10;"
           + "mv z3 ../../z3-" + commit_id)
    execute(cmd)
    return os.path.abspath("z3-" + commit_id)


def get_cvc4_trunk(commit_id):
    execute("git clone https://github.com/cvc5/cvc5 " + commit_id)
    cmd = ("cd " + commit_id + ";"
           + "git checkout " + commit_id + ";"
           + "./contrib/get-antlr-3.4; ./configure.sh "
           + "--static production --assertions --symfpu; cd build;"
           + "make -j 10;"
           + "mv bin/cvc4 ../../cvc4-" + commit_id)
    execute(cmd)
    return os.path.abspath("cvc4-" + commit_id)


def cleanup():
    subprocess.getoutput("rm -rf cvc4*")
    subprocess.getoutput("rm -rf z3*")


cvc4 = get_cvc4_1_8()
z3 = get_z3_trunk("d0515dc")

first_config = z3
second_config = cvc4 + " --strings-exp  -q"
fn = "examples/seed27.smt2"
opts = "-i 1 -c examples/c27.txt"

print("Trying to retrigger soundness bug...", flush=True)

bug_catched = False
for _ in range(400):
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
