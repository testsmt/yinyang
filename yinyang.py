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
    # # ex_type, ex, tb = sys.exc_info()
    fn = inspect.trace()[-1].filename
    lineno = inspect.trace()[-1].lineno
    print("Runtime error at %s:%s" %(fn,lineno))
    print("msg: "+str(e))
    print("cmd: "+ ' '.join(sys.argv))
    print("version: yinyang v0.2.0") #TODO: Do not hardcode
    print("Please file an issue: https://github.com/testsmt/yinyang/issues")
    exit(ERR_INTERNAL)



