import sys
sys.setrecursionlimit(100000)

from antlr4 import *
from antlr4.error.ErrorListener import ErrorListener

from .SMTLIBv2Lexer import SMTLIBv2Lexer
from .SMTLIBv2Parser import *
from .ast_visitor import *

class ErrorListener(ErrorListener):
    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        print("Parser error on line %d column %d." % (line, column))
        exit(1)

def remove_set_logic_status(formula):
    new_cmds = []
    for cmd in formula.commands:
        if isinstance(cmd,SMTLIBCommand) and "(set-info" in cmd.cmd_str:continue
        if isinstance(cmd,SMTLIBCommand) and "(set-logic"  in cmd.cmd_str: continue
        new_cmds.append(cmd)
    formula.commands = new_cmds
    return formula

def parse_file(fn, silent=True):
    fstream = FileStream(fn, encoding = 'utf8')
    ast = None
    if silent:
        try:
            ast = generate_ast(fstream)
        except Exception as e:
            print("Error generating the AST.")
            print(e)
            exit(1)
    else:
         ast = generate_ast(fstream)
    return remove_set_logic_status(ast)

def parse_str(s, silent=True):
    istream = InputStream(s)
    ast = None
    if silent:
        try:
            ast = generate_ast(istream)
        except Exception as e:
            print("Error generating the AST.")
            print(e)
            exit(1)
    else:
        ast = generate_ast(istream)
    return remove_set_logic_status(ast)

def generate_ast(stream):
    error_listener = ErrorListener()
    lexer = SMTLIBv2Lexer(stream)
    lexer.removeErrorListeners()
    lexer.addErrorListener(error_listener)
    stream = CommonTokenStream(lexer)
    parser = SMTLIBv2Parser(stream)
    parser.removeErrorListeners()
    parser.addErrorListener(error_listener)
    tree = parser.start()
    vis = ASTVisitor()
    formula = vis.visitStart(tree)
    return formula
