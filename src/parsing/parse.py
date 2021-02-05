import sys
sys.setrecursionlimit(100000)

import traceback

from antlr4 import *
from antlr4.error.ErrorListener import ErrorListener

from src.parsing.timeout_decorator import *

from .SMTLIBv2Lexer import SMTLIBv2Lexer
from .SMTLIBv2Parser import *
from .ast_visitor import *

class ErrorListener(ErrorListener):
    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        print(e)
        print("Parser error on line %d column %d." % (line, column), flush=True)

def remove_set_logic_status(formula):
    new_cmds = []
    for cmd in formula.commands:
        if isinstance(cmd,SMTLIBCommand) and "(set-info" in cmd.cmd_str:continue
        if isinstance(cmd,SMTLIBCommand) and "(set-logic"  in cmd.cmd_str: continue
        new_cmds.append(cmd)
    formula.commands = new_cmds
    return formula

def generate_ast(stream):
    error_listener = ErrorListener()
    lexer = SMTLIBv2Lexer(stream)
    lexer.removeErrorListeners()
    lexer.addErrorListener(error_listener)
    stream = CommonTokenStream(lexer)
    parser = SMTLIBv2Parser(stream)
    parser.removeErrorListeners()
    tree = parser.start()
    vis = ASTVisitor()
    formula = vis.visitStart(tree)
    return formula, vis.globals

    # empty file or parser preceding parser errror
    if len(formula.commands) == 0:
        return None

    return remove_set_logic_status(formula)


def parse_filestream(fn,timeout_limit):
    @exit_after(timeout_limit)
    def _parse_filestream(fn):
        fstream = FileStream(fn, encoding = 'utf8')
        ast = generate_ast(fstream)
        return ast
    return _parse_filestream(fn)


def parse_inputstream(s,timeout_limit):

    @exit_after(timeout_limit)
    def _parse_inputstream(s):
        istream = InputStream(s)
        ast = generate_ast(istream)
        return ast
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

    try:
        script = parse_fct(arg,timeout_limit)
    except KeyboardInterrupt:
        print("Parser timed out or was interrupted.")
    except Exception as e:
        if not silent:
            print("Error generating the AST.")
            print(e)
            traceback.print_exc(file=sys.stdout)
    return script


def parse_file(fn, timeout_limit=30, silent=True):
    """
    Parse SMT-LIB file.

    :fn: path to SMT-LIB file.
    :silent: if silent=True the parser will withhold stacktrace from user on crash.
    :returns: Script object representing AST of SMT-LIB file. None if timeout
              or crash occurred.
    """
    return parse(parse_filestream, fn, timeout_limit, silent)


def parse_str(s, timeout_limit=30, silent=True):
    """
    Parse SMT-LIB from string.

    :fn: path to SMT-LIB file.
    :silent: if silent=True the parser will withhold stacktrace from user on crash.
    :returns: Script object representing AST of SMT-LIB file. None if timeout
              or crash occurred.
    """
    return parse(parse_inputstream, s, timeout_limit, silent)
