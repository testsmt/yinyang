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

TIME_LIMIT = 180


def run_opfuzz(first_config, second_config, directory, opts, timeout_limit):
    timeout = "timeout --signal=INT " + str(timeout_limit) + " "
    cmd = (
        timeout
        + python
        + " bin/opfuzz "
        + '"'
        + first_config
        + ";"
        + second_config
        + '" '
        + opts
        + " "
        + directory
    )
    output = subprocess.getoutput(cmd)
    generated_seeds = 0
    used_seeds = 0
    ignored_issues = 0
    return output, cmd


def get_cvc4():
    cvc4_link = "https://github.com/CVC4/CVC4/releases/download/1.8/\
cvc4-1.8-x86_64-linux-opt"
    os.system("wget " + cvc4_link)
    subprocess.getoutput("chmod +x cvc4-1.8-x86_64-linux-opt")
    return os.path.abspath("cvc4-1.8-x86_64-linux-opt")


def get_z3():
    z3_link = "https://github.com/Z3Prover/z3/releases/download/z3-4.8.10/\
z3-4.8.10-x64-ubuntu-18.04.zip"
    os.system("wget " + z3_link)
    os.system("unzip z3-4.8.10-x64-ubuntu-18.04.zip")
    return os.path.abspath("z3-4.8.10-x64-ubuntu-18.04/bin/z3")


def cleanup():
    subprocess.getoutput("rm -rf cvc4*")
    subprocess.getoutput("rm -rf z3*")


cleanup()
cvc4 = get_cvc4()
z3 = get_z3()
first_config = z3 + " model_validate=true"
second_config = cvc4 + " --check-models --produce-models --incremental -q"
mock_benchmarks = str(os.path.dirname(os.path.realpath(__file__)))\
    + "/mock_benchmarks"
out, cmd = run_opfuzz(
    first_config, second_config, mock_benchmarks, "-m 1", TIME_LIMIT)
if "3 seeds processed, 1 valid, 2 invalid" not in out:
    print("An error occurred.", flush=True)
    print("cmd", cmd)
    exit(1)
