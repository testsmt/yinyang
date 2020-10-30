#! /usr/bin/python3.7
import sys
from antlr4 import *

from src.args import args
from src.modules.Fuzzer import Fuzzer

fuzzer = Fuzzer(args)
fuzzer.run()
