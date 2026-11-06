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
SMT-LIB logics as sets of features, and inference of the features a script
needs. Used to pick a set-logic command that is valid for a mutant.

Features:
    Q   quantifiers (no "QF_" prefix)
    A   arrays
    UF  uninterpreted functions and sorts
    BV  bit-vectors
    FP  floating-point
    DT  datatypes
    S   strings
    I   integers
    R   reals
    NL  non-linear arithmetic

Division by a literal zero, e.g. (/ x 0.0) or (mod x 0), is undefined in
SMT-LIB (the result is an unspecified value), so (/ x 0.0) is not a
linear term. cvc5 rejects it in linear logics, z3 accepts it. Whether it
counts as non-linear is set by the div_by_zero argument of infer_logic.
"""

import re

from yinyang.src.parsing.Ast import (
    Term,
    DeclareConst,
    DeclareFun,
    DefineConst,
    DefineFun,
    SMTLIBCommand,
)

LOGIC_RE = re.compile(
    r"^(QF_)?(AX|A)?(UF)?(BV)?(FP)?(DT)?(S)?"
    r"(IDL|RDL|LIA|LRA|LIRA|NIA|NRA|NIRA)?$"
)

ARITH_FEATURES = {
    None: [],
    "IDL": ["I"], "LIA": ["I"], "NIA": ["I", "NL"],
    "RDL": ["R"], "LRA": ["R"], "NRA": ["R", "NL"],
    "LIRA": ["I", "R"], "NIRA": ["I", "R", "NL"],
}

SORT_FEATURES = {
    "Int": ["I"],
    "Real": ["R"],
    "BitVec": ["BV"],
    "Array": ["A"],
    "FloatingPoint": ["FP"],
    "Float16": ["FP"],
    "Float32": ["FP"],
    "Float64": ["FP"],
    "Float128": ["FP"],
    "RoundingMode": ["FP"],
    "String": ["S"],
    "RegLan": ["S"],
}

OP_FEATURES = {
    "div": ["I"], "mod": ["I"], "abs": ["I"],
    "/": ["R"],
    "to_real": ["I", "R"], "to_int": ["I", "R"], "is_int": ["I", "R"],
    "select": ["A"], "store": ["A"], "const": ["A"],
    "concat": ["BV"], "extract": ["BV"], "repeat": ["BV"],
    "zero_extend": ["BV"], "sign_extend": ["BV"],
    "rotate_left": ["BV"], "rotate_right": ["BV"],
    "bv2nat": ["BV", "I"], "bv2int": ["BV", "I"], "int2bv": ["BV", "I"],
    "fp": ["FP"], "to_fp": ["FP"], "to_fp_unsigned": ["FP"],
    "+zero": ["FP"], "-zero": ["FP"], "+oo": ["FP"], "-oo": ["FP"],
    "NaN": ["FP"],
}

FP_CONSTANTS = {
    "RNE", "RNA", "RTP", "RTN", "RTZ",
    "roundNearestTiesToEven", "roundNearestTiesToAway",
    "roundTowardPositive", "roundTowardNegative", "roundTowardZero",
}

DECIMAL_RE = re.compile(r"^[0-9]+\.[0-9]+$")
ZERO_RE = re.compile(r"^0+(\.0+)?$")

# Pseudo-feature of _term_features for divisions by a literal zero; it is
# never part of the features returned by infer_logic.
DIV_BY_ZERO = "div0"

DIV_BY_ZERO_MODES = ["nonlinear", "linear", "skip"]


def parse_logic(name):
    """
    Converts an SMT-LIB logic name, e.g. "QF_AUFLIA", into its set of
    features. Difference logics (IDL, RDL) are mapped to LIA and LRA.
    :returns: frozenset of features, or None for logics this module does
              not understand (e.g. "ALL" or solver-specific logics).
    """
    m = LOGIC_RE.match(name)
    if not m or name in ("", "QF_"):
        return None
    qf, arrays, uf, bv, fp, dt, strings, arith = m.groups()
    features = set(ARITH_FEATURES[arith])
    if not qf:
        features.add("Q")
    for flag, feature in [(arrays, "A"), (uf, "UF"), (bv, "BV"), (fp, "FP"),
                          (dt, "DT"), (strings, "S")]:
        if flag:
            features.add(feature)
    return frozenset(features)


def is_difference_logic(name):
    return name.endswith("IDL") or name.endswith("RDL")


def logic_name(features):
    """
    Converts a set of features into the smallest SMT-LIB logic name that
    contains all of them, e.g. {"UF", "I", "NL"} -> "QF_UFNIA".
    """
    name = "" if "Q" in features else "QF_"
    for feature in ["A", "UF", "BV", "FP", "DT", "S"]:
        if feature in features:
            name += feature
    ints, reals = "I" in features, "R" in features
    if ints or reals:
        name += "N" if "NL" in features else "L"
        name += {(True, False): "IA", (False, True): "RA",
                 (True, True): "IRA"}[(ints, reals)]
    if name in ("", "QF_"):
        name += "UF"
    return name


def _sort_features(sort, user_sorts, features):
    for token in re.findall(r"[^\s()]+", str(sort)):
        features.update(SORT_FEATURES.get(token, []))
        if token in user_sorts:
            features.add("UF")


def _op_name(op):
    """
    Returns the name of an operator, e.g. "extract" for "(_ extract 3 0)"
    and "const" for "(as const (Array Int Int))".
    """
    tokens = re.findall(r"[^\s()]+", op)
    if len(tokens) > 1 and tokens[0] in ("_", "as"):
        return tokens[1]
    return tokens[0] if tokens else op


def _is_coefficient(term, ground_lets):
    """
    Checks whether term may be used as a coefficient in linear arithmetic.
    Only numerals, decimals and "-" and "/" over them count, which is what
    z3 accepts (it rejects e.g. (* (+ 1 2) x) in QF_LIA).
    """
    if isinstance(term, str):
        return bool(re.match(r"^[0-9]+(\.[0-9]+)?$", term))
    if term.is_const:
        return True
    if term.is_var:
        return term.name in ground_lets
    if isinstance(term.op, str) and term.op in ("-", "/") and term.subterms:
        return all(_is_coefficient(t, ground_lets) for t in term.subterms)
    return False


def _is_zero(term):
    """Checks whether term is a literal zero, e.g. 0, 0.0 or (- 0)."""
    if isinstance(term, str):
        return bool(ZERO_RE.match(term))
    if term.is_const:
        return bool(ZERO_RE.match(str(term.name)))
    if term.op == "-" and term.subterms and len(term.subterms) == 1:
        return _is_zero(term.subterms[0])
    return False


def _term_features(term, user_sorts, features, ground_lets):
    if term is None or isinstance(term, str):
        return

    if term.is_const:
        name = str(term.name)
        if name.startswith("#b") or name.startswith("#x") or \
           name.startswith("(_ bv"):
            features.add("BV")
        elif name.startswith('"'):
            features.add("S")
        elif DECIMAL_RE.match(name):
            features.add("R")
        elif name in FP_CONSTANTS:
            features.add("FP")
        return

    if term.is_var:
        if term.name in FP_CONSTANTS:
            features.add("FP")
        return

    if term.quantifier:
        features.add("Q")
        _sort_features(" ".join(term.quantified_vars[1]), user_sorts,
                       features)

    if term.let_terms:
        ground_lets = set(ground_lets)
        for var, let_term in zip(term.var_binders, term.let_terms):
            _term_features(let_term, user_sorts, features, ground_lets)
            if _is_coefficient(let_term, ground_lets):
                ground_lets.add(var)
            else:
                ground_lets.discard(var)

    if isinstance(term.op, str):
        name = _op_name(term.op)
        features.update(OP_FEATURES.get(name, []))
        if name.startswith("bv"):
            features.add("BV")
        elif name.startswith("fp."):
            features.add("FP")
        elif name.startswith("str.") or name.startswith("re.") or \
                name in ("int.to.str", "str.to.int"):
            features.add("S")
        if "(as const" in term.op or "(Array" in term.op:
            _sort_features(term.op, user_sorts, features)

        subterms = term.subterms or []
        if name == "*":
            non_coeffs = [t for t in subterms
                          if not _is_coefficient(t, ground_lets)]
            if len(non_coeffs) > 1:
                features.add("NL")
        elif name in ("div", "mod", "/"):
            if any(not _is_coefficient(t, ground_lets)
                   for t in subterms[1:]):
                features.add("NL")
            if any(_is_zero(t) for t in subterms[1:]):
                features.add(DIV_BY_ZERO)

    for sub in term.subterms or []:
        _term_features(sub, user_sorts, features, ground_lets)


def infer_logic(script, div_by_zero="nonlinear"):
    """
    Computes the features a script needs, i.e. the smallest logic in which
    it is valid. The inference is syntactic: it looks at declared sorts,
    operators and literals, not at the types of terms.
    :div_by_zero: "nonlinear" if a division by a literal zero needs
                  non-linear arithmetic (as in cvc5), "linear" (or "skip")
                  if it does not (as in z3)
    :returns: frozenset of features (see the module docstring).
    """
    features = set(_script_features(script))
    if DIV_BY_ZERO in features:
        features.discard(DIV_BY_ZERO)
        if div_by_zero == "nonlinear":
            features.add("NL")
    return frozenset(features)


def divides_by_zero(script):
    """
    Checks whether script divides by a literal zero, e.g. (/ x 0.0) or
    (mod x 0).
    """
    return DIV_BY_ZERO in _script_features(script)


def _script_features(script):
    features = set()
    user_sorts = set()
    for cmd in script.commands:
        if isinstance(cmd, SMTLIBCommand):
            tokens = re.findall(r"[^\s()]+", cmd.cmd_str)
            if not tokens:
                continue
            if tokens[0] == "declare-sort" and len(tokens) > 1:
                user_sorts.add(tokens[1])
                features.add("UF")
            elif tokens[0] in ("declare-datatype", "declare-datatypes"):
                features.add("DT")
                _sort_features(cmd.cmd_str, user_sorts, features)
            elif tokens[0] == "define-sort":
                _sort_features(cmd.cmd_str, user_sorts, features)
        elif isinstance(cmd, DeclareFun):
            if str(cmd.input_sort).strip():
                features.add("UF")
            _sort_features(cmd.input_sort, user_sorts, features)
            _sort_features(cmd.output_sort, user_sorts, features)
        elif isinstance(cmd, DeclareConst):
            _sort_features(cmd.sort, user_sorts, features)
        elif isinstance(cmd, DefineFun):
            _sort_features(cmd.sorted_vars, user_sorts, features)
            _sort_features(cmd.sort, user_sorts, features)
        elif isinstance(cmd, DefineConst):
            _sort_features(cmd.sort, user_sorts, features)

        term = getattr(cmd, "term", None)
        if isinstance(term, Term):
            _term_features(term, user_sorts, features, set())
    return frozenset(features)
