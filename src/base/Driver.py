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
from pathlib import Path
from src.base.Exitcodes import ERR_USAGE, ERR_EXHAUSTED_DISK

path = Path(__file__)
rootpath = str(path.parent.absolute().parent)

try:
    sys.path.insert(1, os.getcwd() + "/.yinyang")
    from Config import solvers
except Exception as e:
    from config.Config import solvers


def check_solver_clis():
    if args.SOLVER_CLIS == "":
        if len(solvers) == 0:
            print("error: no solver specified", flush=True)
            exit(ERR_USAGE)
        args.SOLVER_CLIS = solvers
    else:
        args.SOLVER_CLIS = args.SOLVER_CLIS.split(";") + solvers


def check_timeout():
    if args.timeout <= 0:
        print("error: timeout should not be a negative number or zero",
              flush=True)
        exit(ERR_USAGE)


def check_iterations():
    if args.iterations <= 0:
        print("error: iterations should not be a negative number zero",
              flush=True)
        exit(ERR_USAGE)


def create_bug_folder():
    if not os.path.isdir(args.bugsfolder):
        try:
            os.mkdir(args.bugsfolder)
        except Exception:
            print("error: bug folder cannot be created", flush=True)
            exit(ERR_EXHAUSTED_DISK)


def create_log_folder():
    if not os.path.isdir(args.logfolder):
        try:
            os.mkdir(args.logfolder)
        except Exception:
            print("error: log folder cannot be created", flush=True)
            exit(ERR_EXHAUSTED_DISK)


def create_scratch_folder():
    if not os.path.isdir(args.scratchfolder):
        try:
            os.mkdir(args.scratchfolder)
        except Exception:
            print("error: scratch folder cannot be created", flush=True)
            exit(ERR_EXHAUSTED_DISK)


def get_seeds():
    temp_seeds = []
    for path in args.PATH_TO_SEEDS:
        if not os.path.exists(path):
            print('error: folder/file "%s" does not exist' % (path),
                  flush=True)
            exit(ERR_USAGE)
        if os.path.isfile(path):
            temp_seeds.append(path)
        elif os.path.isdir(path):
            for subdir, dirs, files in os.walk(path):
                for filename in files:
                    filepath = subdir + os.sep + filename
                    if filepath.endswith(".smt2"):
                        temp_seeds.append(filepath)
        else:
            print("error: %s is neither a file nor a directory", flush=True)
            exit(ERR_USAGE)

    args.PATH_TO_SEEDS = temp_seeds


def check_opfuzz():
    if len(args.PATH_TO_SEEDS) < 1:
        print("error: please provide at least one seed", flush=True)
        exit(ERR_USAGE)

    if len(args.SOLVER_CLIS) < 2:
        print("error: please provide at least two SMT solvers", flush=True)
        exit(ERR_USAGE)


def check_fusion():
    if len(args.PATH_TO_SEEDS) < 2:
        print(
            "error: please provide at least two seeds for the fusion strategy",
            flush=True,
        )
        exit(ERR_USAGE)

    if len(args.SOLVER_CLIS) < 1:
        print("error: please provide at one SMT solvers", flush=True)
        exit(ERR_USAGE)


def run_checks(parser, strategy):
    global args
    args = parser.parse_args()
    if not args.PATH_TO_SEEDS:
        parser.error("no seed-file/seed folder specified")

    check_solver_clis()
    check_timeout()
    check_iterations()
    create_bug_folder()
    create_log_folder()
    create_scratch_folder()
    get_seeds()
    if strategy in ["opfuzz", "typefuzz"]:
        check_opfuzz()
    else:
        check_fusion()
    return args
