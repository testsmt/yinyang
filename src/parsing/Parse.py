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
import traceback
import logging

from antlr4.error.ErrorListener import ErrorListener

from src.parsing.SMTLIBv2Lexer import SMTLIBv2Lexer
from src.parsing.SMTLIBv2Parser import SMTLIBv2Parser
from src.parsing.TimeoutDecorator import exit_after
from src.parsing.AstVisitor import AstVisitor

from antlr4.CommonTokenStream import CommonTokenStream
from antlr4.FileStream import FileStream
from antlr4.InputStream import InputStream

sys.setrecursionlimit(100000)


class ErrorListener(ErrorListener):
    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        logging.debug("Parser error on line %d column %d."
                      % (line, column), flush=True)


def prepare_seed(formula):
    """
    Prepare seed script for fuzzing. Remove set-logic, set-info and other
    output-producing commands. Set-logic and set-info may raise warning
    messages from SMT solvers. Output-producing commands may cause errors,
    e.g., get-model, get-proof etc. Errors such as

                (error "line X column Y: msg")

    are ignored to avoid false positives in the bug detection logic. As the bug
    detection logic is based on string matching such errors may lead to
    soundness issues being ignored, e.g. if the error occurred after a faulty
    check-sat result. Hence, we remove all output-producing SMT-LIB commands
    from the script.
    """
    new_cmds = []
    for cmd in formula.commands:
        if "set-info" in cmd.__str__():
            continue
        if "set-logic" in cmd.__str__():
            continue

        # Ignore output-producing commands to make sure the detection logic
        # won't be mislead
        #
        if "get-model" in cmd.__str__():
            continue
        if "get-assertions" in cmd.__str__():
            continue
        if "get-proof" in cmd.__str__():
            continue
        if "get-unsat-assumptions" in cmd.__str__():
            continue
        if "get-unsat-core" in cmd.__str__():
            continue
        if "get-value" in cmd.__str__():
            continue
        if "echo" in cmd.__str__():
            continue
        if "simplify" in cmd.__str__():
            continue
        new_cmds.append(cmd)

    formula.commands = new_cmds
    return formula


def generate_ast(stream, prep_seed=True):
    error_listener = ErrorListener()
    lexer = SMTLIBv2Lexer(stream)
    lexer.removeErrorListeners()
    lexer.addErrorListener(error_listener)
    stream = CommonTokenStream(lexer)
    parser = SMTLIBv2Parser(stream)
    parser.removeErrorListeners()
    tree = parser.start()
    vis = AstVisitor()
    formula = vis.visitStart(tree)

    # empty file or parser preceding parser error
    if len(formula.commands) == 0:
        return None

    return prepare_seed(formula) if prep_seed else formula, vis.global_vars


def parse_filestream(fn, timeout_limit):
    @exit_after(timeout_limit)
    def _parse_filestream(fn):
        fstream = FileStream(fn, encoding="utf8")
        ast, globs = generate_ast(fstream)
        return ast, globs

    return _parse_filestream(fn)


def parse_inputstream(s, timeout_limit):
    @exit_after(timeout_limit)
    def _parse_inputstream(s):
        istream = InputStream(s)
        ast, globs = generate_ast(istream)
        return ast, globs

    return _parse_inputstream(s)


def parse(parse_fct, arg, timeout_limit, silent=True):
    """
    Parser helper function.

    :parse_fct: function to parse stream.
    :arg: first argument to parse_fct.
    :returns: Script object representing AST of SMT-LIB file. None if timeout
              or crash occurred.
    """
    script = None
    globs = None

    try:
        script, globs = parse_fct(arg, timeout_limit)
    except KeyboardInterrupt:
        print("Parser timed out or was interrupted.")
    except Exception as e:
        if not silent:
            print("Error generating the AST.")
            print(e)
            traceback.print_exc(file=sys.stdout)
    return script, globs


def parse_file(fn, timeout_limit=30, silent=True):
    """
    Parse SMT-LIB file.

    :fn: path to SMT-LIB file.
    :silent: if silent=True the parser will withhold stacktrace from user
             on crash.
    :returns: Script object representing AST of SMT-LIB file. None if timeout
              or crash occurred.
    """
    return parse(parse_filestream, fn, timeout_limit, silent)


def parse_str(s, timeout_limit=30, silent=True):
    """
    Parse SMT-LIB from string.

    :fn: path to SMT-LIB file.
    :silent: if silent=True the parser will withhold stacktrace from user
             on crash.
    :returns: Script object representing AST of SMT-LIB file. None if timeout
              or crash occurred.
    """
    return parse(parse_inputstream, s, timeout_limit, silent)
