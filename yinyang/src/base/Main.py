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

"""
Command line entry points of typefuzz, opfuzz and yinyang. They are
installed as console scripts (see setup.cfg), so that an editable install
always runs the current code. The scripts in bin/ call them, to run the
tools from a checkout without installing.
"""

import os
import sys
import signal
import inspect
import importlib

from yinyang.src.base.Driver import run_checks
from yinyang.src.base.Error import raise_runtime_error
from yinyang.src.base import ArgumentParser
from yinyang.src.base.Exitcodes import OK_BUGS, OK_NOBUGS
from yinyang.src.base.Exitcodes import ERR_USAGE, ERR_INTERNAL

from yinyang.src.core.Fuzzer import Fuzzer


def main(tool):
    """
    tool: "typefuzz", "opfuzz" or "yinyang"
    """
    helptext = importlib.import_module(
        "yinyang.config.%sHelptext" % tool.capitalize()
    )
    build_parser = getattr(ArgumentParser, "build_%s_parser" % tool)
    parser = build_parser(os.getcwd(), helptext.usage)

    if len(sys.argv) == 1:

        # Show medium-length description when called without args containing
        # one example and the usage dialogue.
        print(
            helptext.header + "\n\nusage:" + helptext.usage
            + helptext.short_description,
            flush=True,
        )
        exit(ERR_USAGE)

    elif "-h" in sys.argv or "--help" in sys.argv:

        # If called for help, show long description containing general
        # information on the tool, examples with in-depth explanation,
        # and the usage dialogue.
        print(
            helptext.header
            + "\n"
            + helptext.long_description
            + "\n"
            + helptext.options
            + "\n"
            + "usage:"
            + helptext.usage
            + "\n",
            flush=True,
        )
        exit(OK_NOBUGS)

    args = run_checks(parser, tool)
    try:
        fuzzer = Fuzzer(args, tool)

        def exit_with_bugs():
            if fuzzer.statistic.crashes + fuzzer.statistic.soundness == 0:
                exit(OK_NOBUGS)
            exit(OK_BUGS)

        def stats_control_c(sig, frame):
            print("\b\b\rUser interrupt", flush=True)
            fuzzer.statistic.printsum()
            exit_with_bugs()

        def silent_control_c(sig, frame):
            exit_with_bugs()

        if not args.quiet:
            signal.signal(signal.SIGINT, stats_control_c)
        else:
            signal.signal(signal.SIGINT, silent_control_c)

        fuzzer.run()
        exit(OK_NOBUGS)
    except Exception as e:
        trace = inspect.trace()
        raise_runtime_error(trace, sys.argv, e)
        exit(ERR_INTERNAL)


def typefuzz():
    main("typefuzz")


def opfuzz():
    main("opfuzz")


def yinyang():
    main("yinyang")
