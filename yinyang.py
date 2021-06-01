#! /usr/bin/python3.7
import sys
import signal
import logging
from enum import Enum

from src.args import args
from src.modules.Fuzzer import Fuzzer
from src.modules.exitcodes import *

def control_c(sig, frame):
    print("\b\b\rUser interrupt")
    fuzzer.statistic.printsum()
    if fuzzer.statistic.crashes + fuzzer.statistic.soundness == 0:
        exit(OK_NOBUGS)
    exit(OK_BUGS)

signal.signal(signal.SIGINT,control_c)
fuzzer = Fuzzer(args)
fuzzer.run()

