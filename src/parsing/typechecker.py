import sys
sys.setrecursionlimit(100000)

from src.parsing.ast_visitor import *
from src.parsing.parse import *
from src.parsing.types import *

#TODO distinguish arity mismatch from false types
class TypeCheckError(Exception):
    def __init__(self, message):
        self.message="Type Error:"
        super().__init__(self.message)

class MismatchArgumentCount(Exception):
    def __init__(self, message):
        self.message="Type Error:"
        super().__init__(self.message)

"""
(- Int Int)                 ; negation
(- Int Int Int :left-assoc) ; subtraction
(+ Int Int Int :left-assoc)
(* Int Int Int :left-assoc)
(div Int Int Int :left-assoc)
(mod Int Int Int)
(abs Int Int)
(<= Int Int Bool :chainable)
(<  Int Int Bool :chainable)
(>= Int Int Bool :chainable)
(>  Int Int Bool :chainable)
"""

def typecheck_not(expr, ctxt=[]):
    """ (not Bool Bool) """
    if len(expr.subterms) != 1 or typecheck_expr(expr.subterms[0],ctxt) != BOOLEAN_TYPE:
        exit(1)
        #TODO: raise Exception
    return BOOLEAN_TYPE

def typecheck_unary_minus(expr,ctxt=[]):
    """ (- Int Int) """
    """ (- Real Real) """
    if len(expr.subterms) != 1:
        exit(1)
        # TODO: raise Exception
    return typecheck_expr(expr.subterms[0],ctxt)

def typecheck_eq(expr, ctxt=[]):
    """ (par (A) (= A A Bool :chainable))
        (par (A) (distinct A A Bool :pairwise))
    """
    if len(expr.subterms) < 2:
        exit(1)
        # TODO: raise Exception
    typ = typecheck_expr(expr.subterms[0])
    for term in expr.subterms[1:]:
        if typecheck_expr(term) != typ:
            exit(1)
            # TODO: raise Exception
    return BOOLEAN_TYPE

def typecheck_ite(expr, ctxt=[]):
    """ (par (A) (ite Bool A A A)) """
    if len(expr.subterms) < 3:
        exit(1)
    if typecheck_expr(expr.subterms[0]) != BOOLEAN_TYPE and\
        typecheck_expr(expr.subterms[1]) != typecheck_expr(expr.subterms[2]):
        # TODO: raise Exception
        exit(1)
    return typecheck_expr(expr.subterms[1])

def typecheck_nary_bool(expr, ctxt=[]):
    """ (and Bool Bool Bool :left-assoc)
        (or Bool Bool Bool :left-assoc)
        (xor Bool Bool Bool :left-assoc)
    """
    if len(expr.subterms) < 1:
        exit(1)

    for term in expr.subterms[0:]:
        if typecheck_expr(term, ctxt) != BOOLEAN_TYPE:
            exit(1)
    return BOOLEAN_TYPE


def typecheck_expr(expr, ctxt=[]):
    if expr.is_const or expr.is_var or expr.is_indexed_id:
        return expr.type
    if expr.op:
        if expr.op == NOT:
            return typecheck_not(expr,ctxt)
        # TODO: check that it is not the binary case
        if expr.op == UNARY_MINUS:
            return typecheck_unary_minus(expr,ctxt)
        if expr.op in EQ:
            return typecheck_eq(expr,ctxt)
        if expr.op == ITE:
            return typecheck_ite(expr,ctxt)

    # TODO raise exception - type-checking failed
    # in non-strict case, just return Unknown
