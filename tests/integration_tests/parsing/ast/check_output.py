#! /usr/bin/python3.7

import sys
sys.setrecursionlimit(100000)

from antlr4 import *
sys.path.append("../../")

from src.parsing.SMTLIBv2Lexer import SMTLIBv2Lexer
from src.parsing.SMTLIBv2Parser import *
from src.parsing.ast_visitor import *

import random
import string
import subprocess as sp
import os

def random_string(length=5):
    return ''.join(random.sample(string.ascii_letters + string.digits, length))

def ast_gen(fn):
    istream = FileStream(fn,encoding = 'utf8')
    lexer = SMTLIBv2Lexer(istream)
    stream = CommonTokenStream(lexer)
    parser = SMTLIBv2Parser(stream)
    tree = parser.start()
    vis = ASTVisitor()
    script = vis.visitStart(tree)
    return script

def show_diff(inp,parsed):
    with open("input.smt2", "w") as f:
        f.write(inp)

    with open("parsed.smt2", "w") as f:
        f.write(parsed)

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print("Usage: ./check_output.py <smtlib-file>")
        exit(0)
    fn=sys.argv[1]
    parsed_fn=random_string()+".smt2"
    with open(parsed_fn,"w") as f:
        f.write(ast_gen(fn).__str__())
    cmd = "raco read "+parsed_fn
    parsed=sp.getoutput(cmd)
    cmd = "raco read "+fn
    inp = sp.getoutput(cmd)
    os.system("rm -rf "+parsed_fn)
    if inp == parsed: exit(0)
    show_diff(inp,parsed)
    exit(1)
