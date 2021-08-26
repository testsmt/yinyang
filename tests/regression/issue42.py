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
import glob
import subprocess

python = sys.executable


def call_fuzzer(first_config, fn, opts):
    cmd = python + " bin/yinyang "\
        + '"' + first_config + '" ' + opts + " " + fn
    print(cmd)
    output = subprocess.getoutput(cmd)


def cleanup():
    subprocess.getoutput("rm -rf z3*")
    subprocess.getoutput("rm -rf logs")


def get_z3():
    z3_link = (
        "https://github.com/Z3Prover/z3/releases/download/z3-4.8.6/"
        + "z3-4.8.6-x64-ubuntu-16.04.zip"
    )
    os.system("wget " + z3_link)
    os.system("unzip z3-4.8.6-x64-ubuntu-16.04.zip")
    return os.path.abspath("z3-4.8.6-x64-ubuntu-16.04/bin/z3")


cleanup()
print("Download Z3")
z3 = get_z3()
print("Call fuzzer")
call_fuzzer(z3, "tests/regression/53.smt2 tests/regression/55.smt2", "-o sat")

logfile = glob.glob("logs/*")[0]
if "Invalid mutant:ignore_list" in open(logfile).read():
    exit(1)
