#! /usr/bin/python3.7
import sys
sys.setrecursionlimit(100000)

from antlr4 import *
sys.path.append("../../../../")

from src.parsing.SMTLIBv2Lexer import SMTLIBv2Lexer
from src.parsing.SMTLIBv2Parser import *
from src.parsing.ast_visitor import *
from src.parsing.parse import *

def ast_gen(fn):
    istream = FileStream(fn,encoding = 'utf8')
    lexer = SMTLIBv2Lexer(istream)
    stream = CommonTokenStream(lexer)
    parser = SMTLIBv2Parser(stream)
    tree = parser.start()
    vis = ASTVisitor()
    script = vis.visitStart(tree)
    return script

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print("Usage: ./ast.py <smtlib-file>")
        exit(0)
    fn=sys.argv[1]
    try:
        parse_file(fn,silent=False)
    except Exception as e:
        print(e)
        exit(1)

