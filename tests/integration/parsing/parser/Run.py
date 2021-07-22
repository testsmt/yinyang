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

import sys
import subprocess as sp
import os
from multiprocessing import Pool

sys.path.append("../../")
os.system("rm -rf errors.txt timeouts.txt")
BENCHMARK = "/local/disk1/dominik-exp/benchmarks/"

N = 128


def do_parsing(fn):
    if not os.path.exists(fn):
        os.system("rm -rf " + fn)
    cmd = "timeout -s 9 1 python3.7 parse.py " + fn + ";echo $?"
    out = sp.getoutput(cmd)

    # To suppress debug related issues
    if "dbg" in out:
        return 0

    if "137" in out:
        return 137
    if "error" in out or len(out) > 3:
        print(fn)
        print(out)
        return 1
    if "1" in out:
        print(fn)
        print(out)
        return 1
    return 0


def collect(res, files):
    errs, timeouts = [], []
    for i in range(len(res)):
        if res[i] == 1:
            errs.append(files[i])
        if res[i] == 137:
            timeouts.append(files[i])
    return errs, timeouts


def append_to_file(fn, line):
    flag = "a"
    if not os.path.exists(fn):
        flag = "w"
    with open(fn, flag) as f:
        f.write("\n".join(line))


files = sp.getoutput("find " + BENCHMARK + ' -name "*.smt2"').split("\n")
# files = [f[:-1] for f in open("sorted_errors.txt").readlines()]
batch_size = 100
n = len(files) // batch_size
n_err = 0
n_timeout = 0
with Pool(N) as p:
    for i in range(n):
        res = p.map(do_parsing, files[i * batch_size: (i + 1) * batch_size])
        e, t = collect(res, files[i * batch_size: (i + 1) * batch_size])
        n_err += len(e)
        n_timeout += len(t)
        append_to_file("errors.txt", e)
        append_to_file("timeouts.txt", t)
        print(
            (i + 1) * batch_size, "/",
            len(files), "err=", n_err, "timeouts=", n_timeout
        )
