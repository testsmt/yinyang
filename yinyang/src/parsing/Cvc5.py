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

"""
Restrictions of cvc5 on valid SMT-LIB scripts, used by --cvc5-compat.

cvc5 rejects some scripts that are valid SMT-LIB and accepted by z3. The
following restrictions were checked with cvc5 1.4.2:

1. The arguments of re.range must be ground: they must not contain
   constants, variables or applications of declared functions, e.g.
   (re.range x "c") or (re.range (str.from_code (str.len x)) "c"). cvc5
   reports "expecting a constant string term in regexp range". Ground terms
   that evaluate to strings, e.g. (str.from_code 97), are accepted.

2. Variables of sort RegLan must be eliminated by cvc5's preprocessing: each
   RegLan constant that occurs in an assertion must be defined by a top-level
   equation (= r t) (or (= t r), also as a conjunct of a top-level and) in
   which r does not occur in t after the definitions of the other RegLan
   constants are substituted. Otherwise, e.g. (distinct r t), (= r (re.* r)),
   or an equation under or/ite, cvc5 reports "Regular expression variables
   are not supported". Quantified variables of sort RegLan and declared
   functions with arguments and range RegLan are never eliminated.
"""

from yinyang.src.parsing.Ast import (
    Assert, DeclareConst, DeclareFun, Term
)

REGLAN = "RegLan"


def cvc5_unsupported(script):
    """
    :returns: a description of the first restriction of cvc5 (see the module
              docstring) that script violates, or None
    """
    reglan, reason = _reglan_constants(script)
    if reason:
        return reason
    for term in _command_terms(script):
        reason = _check_term(term, {}, reglan)
        if reason:
            return reason
    if reglan:
        return _uneliminated_reglan(script, reglan)
    return None


def _reglan_constants(script):
    """
    :returns: (names of the RegLan constants, reason) where reason is set if
              a function with range RegLan is declared
    """
    names = set()
    for cmd in script.commands:
        if isinstance(cmd, DeclareConst) and str(cmd.sort).strip() == REGLAN:
            names.add(cmd.symbol)
        elif isinstance(cmd, DeclareFun) and \
                str(cmd.output_sort).strip() == REGLAN:
            if str(cmd.input_sort).strip():
                return names, "function %s with range RegLan" % cmd.symbol
            names.add(cmd.symbol)
    return names, None


def _command_terms(script):
    for cmd in script.commands:
        term = getattr(cmd, "term", None)
        if isinstance(term, Term):
            yield term
        for term in getattr(cmd, "terms", None) or []:
            if isinstance(term, Term):
                yield term


def _check_term(term, env, reglan):
    """
    Check restriction 1 and quantified RegLan variables in term.

    env: maps the variables bound in the context of term to True if they
         are let-bound to a ground term
    """
    if isinstance(term, str) or term.is_const or term.is_var:
        return None
    if term.quantifier:
        names, sorts = term.quantified_vars
        if any(str(s).strip() == REGLAN for s in sorts):
            return "quantified variable of sort RegLan"
        env = dict(env)
        env.update((name, False) for name in names)
    if term.var_binders:
        for let_term in term.let_terms:
            reason = _check_term(let_term, env, reglan)
            if reason:
                return reason
        env = dict(env)
        env.update(
            (name, _is_ground(let_term, env))
            for name, let_term in zip(term.var_binders, term.let_terms)
        )
    if term.op == "re.range":
        for arg in term.subterms or []:
            if not _is_ground(arg, env):
                return "re.range argument %s is not ground" % arg
    for sub in term.subterms or []:
        reason = _check_term(sub, env, reglan)
        if reason:
            return reason
    return None


def _is_ground(term, env):
    if isinstance(term, str) or term.is_const:
        return True
    if term.is_var:
        return env.get(term.name, False)
    if isinstance(term.op, Term) or term.quantifier:
        return False
    if term.var_binders:
        if not all(_is_ground(t, env) for t in term.let_terms):
            return False
        env = dict(env)
        env.update((name, True) for name in term.var_binders)
    return all(_is_ground(sub, env) for sub in term.subterms or [])


def _reglan_occurrences(term, reglan, bound=frozenset()):
    """
    :returns: the RegLan constants occurring free in term
    """
    if isinstance(term, str) or term.is_const:
        return set()
    if term.is_var:
        if term.name in reglan and term.name not in bound:
            return {term.name}
        return set()
    names = set()
    if isinstance(term.op, Term):
        names |= _reglan_occurrences(term.op, reglan, bound)
    if term.quantifier:
        bound = bound | set(term.quantified_vars[0])
    if term.var_binders:
        for let_term in term.let_terms:
            names |= _reglan_occurrences(let_term, reglan, bound)
        bound = bound | set(term.var_binders)
    for sub in term.subterms or []:
        names |= _reglan_occurrences(sub, reglan, bound)
    return names


def _conjuncts(term):
    if isinstance(term, Term) and term.op == "and" and not term.label:
        for sub in term.subterms:
            yield from _conjuncts(sub)
    else:
        yield term


def _side(term, reglan):
    """
    One side of an equation: ("var", r) for a RegLan constant r, and
    ("term", names) for any other term with the RegLan constants names.
    """
    if term.is_var and term.name in reglan:
        return ("var", term.name)
    return ("term", frozenset(_reglan_occurrences(term, reglan)))


def _uneliminated_reglan(script, reglan):
    """
    Check restriction 2: eliminate the RegLan constants with the top-level
    equations, as cvc5's preprocessing does, until no equation defines a
    further constant.
    """
    used, equations = set(), []
    for cmd in script.commands:
        if not isinstance(cmd, Assert):
            continue
        used |= _reglan_occurrences(cmd.term, reglan)
        for conj in _conjuncts(cmd.term):
            if conj.op == "=" and len(conj.subterms) == 2:
                equations.append(
                    tuple(_side(sub, reglan) for sub in conj.subterms)
                )
    if not used:
        return None

    definitions = {}

    def resolve(side):
        kind, value = side
        if kind == "var":
            if value in definitions:
                return resolve(definitions[value])
            return side
        names = set()
        for name in value:
            kind2, value2 = resolve(("var", name))
            names |= {value2} if kind2 == "var" else value2
        return ("term", frozenset(names))

    changed = True
    while changed:
        changed = False
        for eq in list(equations):
            a, b = resolve(eq[0]), resolve(eq[1])
            for var, other in ((a, b), (b, a)):
                if var[0] != "var":
                    continue
                if (other[0] == "var" and other[1] != var[1]) or \
                        (other[0] == "term" and var[1] not in other[1]):
                    definitions[var[1]] = other
                    equations.remove(eq)
                    changed = True
                    break

    for name in sorted(used):
        if resolve(("var", name)) != ("term", frozenset()):
            return "RegLan constant %s is not eliminated" % name
    return None
