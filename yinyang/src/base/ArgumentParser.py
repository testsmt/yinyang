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
import argparse

from yinyang.src.base.Exitcodes import ERR_USAGE
from yinyang.src.base.Version import VERSION, COMMIT

from pathlib import Path

path = Path(__file__)
ROOTPATH = str(path.parent.absolute().parent.parent.parent)
sys.path.append(ROOTPATH)


class ArgumentParser(argparse.ArgumentParser):
    def error(self, message):
        print("usage:" + self.usage, flush=True)
        self.exit(
            ERR_USAGE,
            "error: %s\nFor a listing of options, use %s --help.\n"
            % (message, self.prog),
        )


def add_common_args(parser, rootpath, current_dir):
    parser.add_argument(
        "SOLVER_CLIS",
        metavar="solver_clis",
    )
    parser.add_argument(
        "PATH_TO_SEEDS",
        nargs="+",
        metavar="seed_file/seed_folder",
    )
    parser.add_argument(
        "-l",
        "--logfolder",
        metavar="path_path_to_folder",
        default=current_dir + "/logs",
    )
    parser.add_argument(
        "-h",
        "--help",
        action="help",
        default=argparse.SUPPRESS,
    )
    parser.add_argument(
        "-t",
        "--timeout",
        default=8,
        metavar="secs",
        type=int,
    )
    parser.add_argument(
        "-b",
        "--bugsfolder",
        metavar="path_to_folder",
        default=current_dir + "/bugs",
    )
    parser.add_argument(
        "-k"
        "--keep-seeds",
        action="store_true",
    )
    parser.add_argument(
        "-s",
        "--scratchfolder",
        metavar="path_to_folder",
        default=current_dir + "/scratch",
    )
    parser.add_argument(
        "-q",
        "--quiet",
        action="store_true",
    )
    parser.add_argument(
        "-n",
        "--no-log",
        action="store_true",
    )
    parser.add_argument(
        "-L",
        "--file-size-limit",
        metavar="num_bytes",
        default=100000,
        type=int,
    )


def add_opfuzz_args(parser, rootpath, current_dir):
    parser.add_argument(
        "-i",
        "--iterations",
        default=300,
        metavar="<N>",
        type=int,
    )
    parser.add_argument(
        "-m",
        "--modulo",
        default=2,
        metavar="<N>",
        type=int,
    )
    parser.add_argument(
        "-v",
        "--version",
        action="version",
        version="opfuzz " + VERSION + " " + "(" + COMMIT + ")",
    )
    parser.add_argument(
        "-c",
        "--config",
        metavar="path_to_file",
        default=rootpath + "/yinyang/config/operator_mutations.txt",
    )


def add_typefuzz_args(parser, rootpath, current_dir):
    parser.add_argument(
        "-i",
        "--iterations",
        default=300,
        metavar="<N>",
        type=int,
    )
    parser.add_argument(
        "-m",
        "--modulo",
        default=2,
        metavar="<N>",
        type=int,
    )
    parser.add_argument(
        "-v",
        "--version",
        action="version",
        version="typefuzz " + VERSION,
    )
    parser.add_argument(
        "-c",
        "--config",
        metavar="path_to_file",
        default=rootpath + "/yinyang/config/typefuzz_config.txt",
    )


def add_yinyang_args(parser, rootpath, current_dir):
    parser.add_argument(
        "-o",
        "--oracle",
        default="sat",
        metavar="{sat,unsat}",
        type=str,
    )
    parser.add_argument(
        "-i",
        "--iterations",
        default=30,
        metavar="<N>",
        type=int,
    )
    parser.add_argument(
        "-v",
        "--version",
        action="version",
        version="yinyang " + VERSION + " " + "(" + COMMIT + ")",
    )
    parser.add_argument(
        "-c",
        "--config",
        metavar="path_to_file",
        default=rootpath + "/yinyang/config/fusion_functions.txt",
    )
    parser.add_argument(
        "-r",
        "--randomize",
        action='store_true',
    )


def build_opfuzz_parser(current_dir, usage):
    parser = ArgumentParser(
        description="",
        usage=usage,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        add_help=False,
    )
    add_common_args(parser, ROOTPATH, current_dir)
    add_opfuzz_args(parser, ROOTPATH, current_dir)

    return parser


def build_typefuzz_parser(current_dir, usage):
    parser = ArgumentParser(
        description="",
        usage=usage,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        add_help=False,
    )
    add_common_args(parser, ROOTPATH, current_dir)
    add_typefuzz_args(parser, ROOTPATH, current_dir)

    return parser


def build_yinyang_parser(current_dir, usage):
    parser = ArgumentParser(
        description="",
        usage=usage,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        add_help=False,
    )
    add_common_args(parser, ROOTPATH, current_dir)
    add_yinyang_args(parser, ROOTPATH, current_dir)

    return parser
