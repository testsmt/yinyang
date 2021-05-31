#! /usr/bin/python3.7
import sys
import signal
import logging

from src.args import args
from src.modules.Fuzzer import Fuzzer

def control_c(sig, frame):
    print("\b\b\rUser interrupt")
    fuzzer.statistic.printsum()
    sys.exit(0)

signal.signal(signal.SIGINT,control_c)
fuzzer = Fuzzer(args)
fuzzer.run()

