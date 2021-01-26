#! /usr/bin/python3.8
import sys

sys.path.append("../../../../")

from src.parsing.ast import *
from src.parsing.parse import *
from src.parsing.typechecker import *

if len(sys.argv) != 2:
    print("Usage check.py <smtlib-file>")
    exit(1)

formula,globs = parse_file(sys.argv[1],False)
terms = []
for cmd in formula.commands:
    if isinstance(cmd, Assert):
        terms.append(cmd.term)
ctxt=Context(globs,{})
for t in terms:
    try:
        typecheck_expr(t,ctxt)
    except Exception as e:
        print(e)
        exit(1)




