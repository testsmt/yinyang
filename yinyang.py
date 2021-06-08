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
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

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
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

#! /usr/bin/python3.7
import sys
import signal
import os
import inspect
import logging
from enum import Enum

from src.args import args
from src.modules.Fuzzer import Fuzzer
from src.modules.exitcodes import *

def print_stats():
    fuzzer.statistic.printsum()
    if fuzzer.statistic.crashes + fuzzer.statistic.soundness == 0:
        exit(OK_NOBUGS)
    exit(OK_BUGS)


def control_c(sig, frame):
    print("\b\b\rUser interrupt")
    print_stats()

signal.signal(signal.SIGINT, control_c)

try:
    fuzzer = Fuzzer(args)
    fuzzer.run()
except Exception as e:
    fn = inspect.trace()[-1].filename
    lineno = inspect.trace()[-1].lineno
    print("Runtime error at %s:%s" %(fn,lineno))
    print("msg: "+str(e))
    print("cmd: "+ ' '.join(sys.argv[:-2])+" "+'"'+ sys.argv[-2] +'"'+" "+sys.argv[-1])
    print("version: yinyang v0.2.0") #TODO: Do not hardcode
    print("Please file an issue: https://github.com/testsmt/yinyang/issues")
    exit(ERR_INTERNAL)



