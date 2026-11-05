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

import copy

from yinyang.src.parsing.Ast import Term
from yinyang.src.parsing.Types import UNKNOWN


def get_subterms(expr):
    """
    Get all subexpression of term object expr.
    :returns: av_expr list of expressions
              expr_types list of types
              (s.t. expression e = av_expr[i] has type expr_types[i])
    """
    av_expr = []
    expr_types = []
    if isinstance(expr, Term):
        if expr.subterms:
            for s in expr.subterms:
                new_av, new_type = get_subterms(s)
                av_expr += new_av
                expr_types += new_type
            new_type = expr.type
            expr_types.append(new_type)
            av_expr.append(expr)
        else:
            av_expr.append(expr)
            expr_types.append(expr.type)
    else:
        if expr.term:
            new_av, new_type = get_subterms(expr.term)
            av_expr += new_av
            expr_types += new_type
    return av_expr, expr_types


def get_all_subterms(formula):
    """
    Get all expressions within a formula and their types.
    :returns: av_expr list of expressions
              expr_types list of types
              (s.t. expression e = av_expr[i] has type expr_types[i])
    """
    av_expr = []
    expr_type = []
    for i in range(len(formula.assert_cmd)):
        exps, typ = get_subterms(formula.assert_cmd[i])
        av_expr += exps
        expr_type += typ
    return av_expr, expr_type


def get_unique_subterms(formula):
    """
    Get all the unique expressions within a formula, grouped by type.
    Any type is supported (Bool, Int, (_ BitVec 8), (Array Int Int), user
    sorts, ...); expressions of unknown type are left out.
    :returns: unique_expr dict mapping each type to the list of unique
              expressions of that type, in order of first occurrence
    """
    av_expr, expr_type = get_all_subterms(formula)

    unique_expr = {}
    for expr, typ in zip(av_expr, expr_type):
        if typ is None or typ == UNKNOWN:
            continue
        exprs = unique_expr.setdefault(typ, [])
        if not any(expr == e for e in exprs):
            exprs.append(copy.deepcopy(expr))
    return unique_expr


def local_defs(term, local):
    """
    term: term object
    local: list of local variables defined in the parent terms

    :returns: list of local variables to be considered within the term
    """
    term = term.parent
    if term:
        if term.quantifier:
            for q_var in term.quantified_vars[0]:
                local.add(q_var)
        if term.let_terms:
            for var in term.var_binders:
                local.add(var)
        if term.parent:
            local_defs(term, local)
    return local


def local_compatible(t1, t2):
    """
    t1: term object
    t2: term object

    :returns: local compatibility of t2 for t, e.g. ,every local variables in
              t2 is defined in t1
    """
    loc_t1 = local_defs(t1, set())
    loc_t2 = local_defs(t2, set())
    return loc_t2.issubset(loc_t1)
