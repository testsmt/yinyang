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

Division by zero, e.g. (/ x 0.0), (mod x 0) or (/ 1 (- 5 5)), is undefined
in SMT-LIB (the result is an unspecified value), so (/ x 0.0) is not a
linear term. cvc5 rejects it in linear logics, z3 accepts a literal zero.
Whether it counts as non-linear is set by the div_by_zero argument of
infer_logic.
"""

import re
from fractions import Fraction

from yinyang.src.parsing.Types import REAL_TYPE
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
NUMBER_RE = re.compile(r"^[0-9]+(\.[0-9]+)?$")

# Larger values (in bits) are not computed by _value, see there.
MAX_VALUE_BITS = 4096

# Pseudo-feature of _term_features for divisions by zero; it is
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

    The only SMT-LIB logics with strings are QF_S, QF_SLIA and QF_SNIA.
    Other names with strings, e.g. QF_SNRA or QF_UFSLIA, are not known to
    z3 (it then has no String sort) and lack the integers that strings need
    (str.len), so ALL is used for strings with any other feature.
    """
    if "S" in features:
        if not features <= {"S", "I", "NL"}:
            return "ALL"
        if "NL" in features:
            return "QF_SNIA"
        return "QF_SLIA" if "I" in features else "QF_S"
    name = "" if "Q" in features else "QF_"
    for feature in ["A", "UF", "BV", "FP", "DT"]:
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
    Checks whether term may be used as a coefficient (a factor or divisor)
    in linear arithmetic. Only what z3 accepts counts: numerals and
    decimals, unary "-" of a coefficient, and (/ a b) where a and b are
    numerals or decimals, possibly negated. z3 rejects e.g. (* (+ 1 2) x),
    (* (- 5 2) x), (div x (- 5 2)), (* (/ (/ 1.0 2.0) 3.0) x) and
    (/ x (/ 1.0 2.0 3.0)) in linear logics. cvc5 accepts all ground terms.

    ground_lets: maps the let variables bound to ground terms to
                 (is_coefficient, value), see _value
    """
    if isinstance(term, str):
        return bool(NUMBER_RE.match(term))
    if term.is_const:
        return True
    if term.is_var:
        return ground_lets.get(term.name, (False, None))[0]
    if not isinstance(term.op, str) or not term.subterms:
        return False
    if term.op == "-" and len(term.subterms) == 1:
        return _is_coefficient(term.subterms[0], ground_lets)
    if term.op == "/" and len(term.subterms) == 2:
        return all(_is_signed_number(t) for t in term.subterms)
    return False


def _is_signed_number(term):
    """Checks whether term is a numeral or decimal, possibly negated."""
    if isinstance(term, str):
        return bool(NUMBER_RE.match(term))
    if term.is_const:
        return bool(NUMBER_RE.match(str(term.name)))
    if term.op == "-" and term.subterms and len(term.subterms) == 1:
        sub = term.subterms[0]
        return isinstance(sub, str) and bool(NUMBER_RE.match(sub)) or \
            not isinstance(sub, str) and sub.is_const and \
            bool(NUMBER_RE.match(str(sub.name)))
    return False


def _value(term, ground_lets):
    """
    The value of a ground arithmetic term over numerals and decimals, e.g.
    0 for (- 5 5), computed with exact rationals.

    ground_lets: see _is_coefficient
    :returns: a Fraction, or None if term is not such a term, divides by
              zero, or a value exceeds MAX_VALUE_BITS (only possible with
              deeply nested products, which are not worth the time)
    """
    if isinstance(term, str):
        return Fraction(term) if NUMBER_RE.match(term) else None
    if term.is_const:
        name = str(term.name)
        return Fraction(name) if NUMBER_RE.match(name) else None
    if term.is_var:
        return ground_lets.get(term.name, (False, None))[1]
    if not isinstance(term.op, str) or not term.subterms:
        return None
    args = []
    for sub in term.subterms:
        v = _value(sub, ground_lets)
        if v is None:
            return None
        args.append(v)
    op = term.op
    if op == "-" and len(args) == 1:
        v = -args[0]
    elif op in ("+", "-", "*"):
        v = args[0]
        for a in args[1:]:
            v = v + a if op == "+" else v - a if op == "-" else v * a
    elif op in ("/", "div", "mod"):
        v = args[0]
        for a in args[1:]:
            if a == 0:
                return None
            if op == "/":
                v = v / a
            else:
                # SMT-LIB: the remainder is non-negative.
                q = v // a if a > 0 else -(v // -a)
                v = q if op == "div" else v - a * q
    elif op == "abs" and len(args) == 1:
        v = abs(args[0])
    elif op in ("to_real", "to_int") and len(args) == 1:
        v = args[0] if op == "to_real" else Fraction(args[0].__floor__())
    else:
        return None
    if max(v.numerator.bit_length(),
           v.denominator.bit_length()) > MAX_VALUE_BITS:
        return None
    return v


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
        ground_lets = dict(ground_lets)
        for var, let_term in zip(term.var_binders, term.let_terms):
            _term_features(let_term, user_sorts, features, ground_lets)
            ground_lets[var] = (_is_coefficient(let_term, ground_lets),
                                _value(let_term, ground_lets))

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
            if any(_value(t, ground_lets) == 0 for t in subterms[1:]):
                features.add(DIV_BY_ZERO)

    for sub in term.subterms or []:
        _term_features(sub, user_sorts, features, ground_lets)


NUMERAL_RE = re.compile(r"^[0-9]+$")


def is_real_logic(name):
    """Checks whether the logic name has reals but no integers, e.g. QF_LRA."""
    features = parse_logic(name) if name else None
    return features is not None and "R" in features and "I" not in features


def numerals_to_decimals(script):
    """
    Rewrites the numerals of script as decimals, e.g. 16 as 16.0. In a logic
    with reals but no integers (e.g. QF_LRA) numerals are reals, but in a
    logic with both (e.g. QF_NIRA or ALL) they are integers. Seeds of real
    logics are rewritten so that they stay well-typed when a mutant needs a
    logic with integers, e.g. (ite c x 1) with x Real, which cvc5 rejects in
    QF_NIRA. Indices, e.g. of (_ extract 3 0), are not terms and stay as is.
    """
    def rewrite(term):
        if term is None or isinstance(term, str):
            return
        if term.is_const and not term.is_indexed_id \
                and isinstance(term.name, str) and NUMERAL_RE.match(term.name):
            term.name += ".0"
            term.type = REAL_TYPE
        for sub in (term.let_terms or []) + (term.subterms or []):
            rewrite(sub)

    for cmd in script.commands:
        terms = list(getattr(cmd, "terms", None) or [])
        if getattr(cmd, "term", None) is not None:
            terms.append(cmd.term)
        for term in terms:
            if isinstance(term, Term):
                rewrite(term)


# Sorts that z3 or cvc5 have built in with (set-logic ALL), so that a
# script declaring a sort of this name is rejected under ALL although it is
# valid in a logic without that theory, e.g. (declare-sort Set 0) in QF_UF.
ALL_BUILTIN_SORTS = {
    "Set", "Seq", "Array", "BitVec", "FloatingPoint", "RoundingMode",
    "String", "RegLan", "Int", "Real", "UnitTuple",
}


def infer_logic(script, div_by_zero="nonlinear"):
    """
    Computes the features a script needs, i.e. the smallest logic in which
    it is valid. The inference is syntactic: it looks at declared sorts,
    operators and literals, not at the types of terms.
    :div_by_zero: "nonlinear" if a division by zero needs non-linear
                  arithmetic (as in cvc5), "linear" (or "skip") if it does
                  not (as in z3). A divisor that is not a coefficient, e.g.
                  (- 5 5), always needs it (see _is_coefficient).
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
    Checks whether script divides by zero, e.g. (/ x 0.0), (mod x 0) or
    (/ 1 (- 5 5)).
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
            _term_features(term, user_sorts, features, {})
    return frozenset(features)
