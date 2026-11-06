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

from yinyang.src.parsing.Ast import (
    Assert, DeclareConst, DeclareFun, DefineConst, DefineFun, DefineFunRec,
    DefineFunsRec, Pop, Push, Term
)
from yinyang.src.parsing.Types import UNKNOWN, sort2type


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


def binder_types(term):
    """
    term: term object

    :returns: dict mapping the variables bound by the quantifiers and lets
              enclosing term to their types; for a name bound more than
              once, the innermost binding
    """
    env = {}
    child, node = term, term.parent
    while node is not None:
        if node.quantifier:
            for name, sort in zip(*node.quantified_vars):
                env.setdefault(name, sort2type(sort))
        elif node.var_binders and not any(
            child is t for t in node.let_terms
        ):
            # let bindings are not in scope in the bound terms
            for name, t in zip(node.var_binders, node.let_terms):
                env.setdefault(name, t.type)
        child, node = node, node.parent
    return env


def free_symbols(term):
    """
    term: term object

    :returns: (variables, functions) where variables maps the variables
              occurring free in term to their types and functions is the
              set of the declared functions applied in term
    """
    variables, functions = {}, set()

    def visit(t, bound):
        if isinstance(t, str) or t.is_const:
            return
        if t.is_var:
            if t.name not in bound:
                variables.setdefault(t.name, t.type)
            return
        if isinstance(t.op, Term):
            functions.add(t.op.name)
        if t.quantifier:
            bound = bound | set(t.quantified_vars[0])
        if t.var_binders:
            for let_term in t.let_terms:
                visit(let_term, bound)
            bound = bound | set(t.var_binders)
        for sub in t.subterms or []:
            visit(sub, bound)

    visit(term, frozenset())
    return variables, functions


def defines_names(term):
    """
    term: term object

    :returns: True if term contains a (! ... :named n) attribute, i.e. a
              copy of term would define n a second time
    """
    if isinstance(term, str):
        return False
    if term.label and any(key == ":named" for key, _ in term.label):
        return True
    return any(defines_names(sub) for sub in term.subterms or [])


def declared_symbols(cmd):
    """
    :returns: the symbols declared or defined by the command cmd
    """
    if isinstance(cmd, (DeclareConst, DeclareFun, DefineConst, DefineFun,
                        DefineFunRec)):
        return [cmd.symbol]
    if isinstance(cmd, DefineFunsRec):
        return [decl.symbol for decl in cmd.fun_decls]
    return []


def num_levels(cmd):
    """
    :returns: the number of assertion levels pushed or popped by cmd
    """
    if cmd.terms:
        try:
            return int(str(cmd.terms[0]))
        except ValueError:
            pass
    return 1


def visible_symbols(commands):
    """
    Determine which declared symbols each assert can use: a symbol is
    visible after its declaration until the pop of the assertion level it
    was declared in.

    :returns: (visible, declared) where visible maps id(assert.term) to the
              set of symbols visible in the assert and declared is the set
              of all declared symbols
    """
    levels = [set()]
    declared = set()
    visible = {}
    current = frozenset()
    for cmd in commands:
        symbols = declared_symbols(cmd)
        if symbols:
            levels[-1].update(symbols)
            declared.update(symbols)
            current = None
        elif isinstance(cmd, Push):
            levels += [set() for _ in range(num_levels(cmd))]
        elif isinstance(cmd, Pop):
            n = min(num_levels(cmd), len(levels) - 1)
            if n > 0:
                del levels[-n:]
                current = None
        elif isinstance(cmd, Assert):
            if current is None:
                current = frozenset().union(*levels)
            visible[id(cmd.term)] = current
    return visible, declared
