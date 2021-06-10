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
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

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

