import sys
sys.setrecursionlimit(100000)

from src.parsing.ast_visitor import *
from src.parsing.parse import *

BOOLEAN_TYPE="bool"
REAL_TYPE="real"
INTEGER_TYPE="integer"
ROUNDINGMODE_TYPE="roundingmode"
STRING_TYPE="string"
REGEXP_TYPE="regex"

NOT="not"
AND="and"
IMPLIES="=>"
OR="or"
XOR="xor"
EQUAL="="
DISTINCT="distinct"
ITE="ite"

POLYMORPHIC_EQ=[EQUAL,DISTINCT]
RT_BOOL=[NOT, AND, IMPLIES, OR, XOR]


"""
[OK] (not Bool Bool)
(=> Bool Bool Bool :right-assoc)
(and Bool Bool Bool :left-assoc)
(or Bool Bool Bool :left-assoc)
(xor Bool Bool Bool :left-assoc)
[OK] (par (A) (= A A Bool :chainable))
[OK] (par (A) (distinct A A Bool :pairwise))
(par (A) (ite Bool A A A))
"""
#TODO distinguish arity mismatch from false types

#TODO
class TypeCheckError(Exception):
    def __init__(self, message):
        self.message="Type Error:"
        super().__init__(self.message)

class MismatchArgumentCount(Exception):
    def __init__(self, message):
        self.message="Type Error:"
        super().__init__(self.message)

def typecheck_not(expr, ctxt=[]):
    """ (not Bool Bool) """
    if len(expr.subterms) == 1 and typecheck_expr(expr.subterms[0],ctxt) == BOOLEAN_TYPE:
        return BOOLEAN_TYPE
    #TODO: raise some meaningful exception
    # as in the AST case: raise ASTException("No match for identifier: ... |... |... ")

def typecheck_poly_eq(expr, ctxt=[]):
    """ (par (A) (= A A Bool :chainable))
        (par (A) (distinct A A Bool :pairwise))
    """
    if len(expr.subterms) < 2:
        raise MismatchArgumentCount("")

    typ = typecheck_expr(expr.subterms[0])
    for term in expr.subterms[1:]:
        if typecheck_expr(term) != typ:
            print()
            raise TypeCheckError("")
    return typ

def typecheck_expr(expr, ctxt=[]):
    print(expr)
    if expr.is_const or expr.is_var or expr.is_indexed_id:
        return expr.type
    if expr.op:
        if expr.op == NOT:
            return typecheck_not(expr,ctxt)
        if expr.op in POLYMORPHIC_EQ:
            return typecheck_poly_eq(expr,ctxt)

    # TODO: return here a generic unknown type
