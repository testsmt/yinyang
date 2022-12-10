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

import enum
import random
import copy
import re
import string

from yinyang.src.parsing.Ast import (
    Const, Var, Expr, Assert, DeclareConst, DeclareFun, Script
)
from yinyang.src.parsing.Types import (
    BITVECTOR_TYPE,
    BOOLEAN_TYPE,
    INTEGER_TYPE,
    REAL_TYPE,
    STRING_TYPE,
)


constant_name_pattern = re.compile(r"^c[0-9]*$")


def gen_random_string(length):
    """
    Generate random string.
    """
    letters = string.ascii_lowercase
    return "".join(random.choice(letters) for i in range(length))


def get_first_assert_idx(template):
    """
    Find first assert's idx.
    """
    for first_ass_idx, cmd in enumerate(template.commands):
        if isinstance(cmd, Assert):
            return first_ass_idx
    return -1


def get_last_assert_idx(template):
    """
    Find last assert's idx.
    """
    last_idx = len(template.commands)
    for i, cmd in enumerate(template.commands):
        if isinstance(cmd, Assert):
            last_idx = i

    return last_idx


def get_first_constant_idx(template):
    """
    Finds first constant index in the template or -1 if none found.
    :template:
    :returns: returns index of first constant and -1 if there is no constant
    """
    for idx, decl in enumerate(template.commands):
        if not isinstance(decl, DeclareConst):
            break
        if constant_name_pattern.match(decl.symbol) is not None:
            return idx
    return -1


def get_last_constant_idx(template):
    """
    Finds last constant index in the template or -1 if none found.
    :template:
    :returns: returns index of last constant and -1 if there is no constant
    """
    last_idx = -1
    for i, decl in enumerate(template.commands):
        if isinstance(decl, DeclareConst) and \
                constant_name_pattern.match(decl.symbol) is not None:
            last_idx = i

    return last_idx


def get_constant_idx(template):
    """
    Checks whether template has a constant to be filled.
    :template:
    :returns: returns index of constant and -1 if there is no constant
    """
    for idx, decl in enumerate(template.commands):
        if not isinstance(decl, DeclareConst):
            break
        if decl.symbol == "c":
            return idx
    return -1


def get_constant_value(declare_const):
    """
    :declare_const: DeclareConst statement specifying the random constant
    :returns: expression for random constant
    """
    const_type = declare_const.sort

    if const_type == INTEGER_TYPE:
        r = random.randint(-1000, 1000)
        if r < 0:
            return Expr(op="-",
                        subterms=[Const(name=str(-r), type=const_type)])
        else:
            return Const(name=str(r), type=const_type)

    if const_type == REAL_TYPE:
        r = round(random.uniform(-1000, 1000), 5)
        if r < 0:
            return Expr(op="-",
                        subterms=[Const(name=str(-r), type=const_type)])
        else:
            return Const(str(r), type=const_type)

    if const_type == BOOLEAN_TYPE:
        return Const(random.choice(["true", "false"]), type=const_type)

    if const_type == STRING_TYPE:
        length = random.randint(0, 20)
        return Const('"' + gen_random_string(length) + '"', type=const_type)

    if isinstance(const_type, BITVECTOR_TYPE):
        length = const_type.bitwidth
        return Const(
            f"#b{random.getrandbits(length):0{length}b}",
            type=const_type,
        )


def get_variables_by_sort(template):
    m = {}
    for _, decl in enumerate(template.commands):
        if not isinstance(decl, DeclareConst):
            break
        if decl.symbol == "z":
            break
        if constant_name_pattern.match(decl.symbol) is not None:
            break
        if str(decl.sort) not in m:
            m[str(decl.sort)] = [decl]
        else:
            m[str(decl.sort)].append(decl)
    return m


def fill_template(xs, ys, z_name, template):
    """
    Binds the variable name to the template.
    :xs: variable names of first formula
    :ys: variable names of second formula
    :returns: bindded template
    """
    # xs and ys map variables to template variable names.
    filled_template = copy.deepcopy(template)
    first_ass_idx = get_first_assert_idx(filled_template)
    z = Var(z_name, z_sort(template))

    # Detect whether template includes random variable c
    first_random_constant_idx = get_first_constant_idx(template)
    if first_random_constant_idx != -1:
        last_random_constant_idx = get_last_constant_idx(template)
        assert first_ass_idx == last_random_constant_idx + 1
        for i in range(first_random_constant_idx,
                       last_random_constant_idx + 1):
            declare_const = template.commands[i]
            const_type = declare_const.sort
            const_expr = get_constant_value(declare_const)

            for ass in filled_template.commands[first_ass_idx:]:
                ass.term.substitute(
                    Var(declare_const.symbol, const_type), const_expr)

    # Bind occurrences of variables to template
    for ass in filled_template.commands[first_ass_idx:]:
        ass.term.substitute(Var("z", z.type), z)
        for x in xs:
            # To be valid, an assignment of variables of the
            # template variables to the seeds variables
            # preserve the sort.
            ass.term.substitute(Var(xs[x].symbol, xs[x].sort),
                                Var(x, [xs[x]].sort))
        for y in ys:
            ass.term.substitute(Var(ys[y].symbol, ys[y].sort),
                                Var(y, ys[y].sort))

    return filled_template


def get_z_idx(template) -> int:
    """
    :returns: the index of the output variable z.
    """
    for idx, decl in enumerate(template.commands):
        if not isinstance(decl, DeclareConst):
            break
        if constant_name_pattern.match(decl.symbol) is not None:
            break
    return idx - 1


def get_variable_by_idx(template, idx: int):
    if (get_z_idx(template) > idx):
        ValueError('Parameter variables come before than ' +
                   'the output variable.')
    return template.commands[idx]


def get_variable_sort_by_idx(template, idx: int):
    return get_variable_by_idx(template, idx).sort


def x_sort(template):
    """
    returns: returns the sort of variable x
    """
    if template.commands[0].symbol != 'x':
        ValueError('Expected x variable declaration as first ' +
                   'command in the fusion function.')
    return template.commands[0].sort


def y_sort(template):
    """
    returns: returns the sort of variable y
    """
    if template.commands[1].symbol != 'y':
        ValueError(
            'Expected y variable declaration as ' +
            'second command in the fusion function.')
    return template.commands[1].sort


def z_sort(template):
    """
    returns: returns the sort of variable z
    """
    z_idx = get_z_idx(template)
    if template.commands[z_idx].symbol != 'z':
        ValueError(
            'Expected z variable declaration to appear as ' +
            z_idx + ' command in the fusion function.')
    return template.commands[z_idx].sort


def inv_by_name(template, name: str):
    for idx, decl in enumerate(template.commands):
        if (decl.symbol != name):
            continue
        if not isinstance(decl, DeclareConst):
            break
        if constant_name_pattern.match(decl.symbol) is not None:
            break
    idx = get_first_assert_idx(template) + idx + 1
    return template.commands[idx]


def variables_to_decls(template):
    m = {}
    for idx, decl in enumerate(template.commands):
        if not isinstance(decl, DeclareConst):
            break
        if constant_name_pattern.match(decl.symbol) is not None:
            break
        m[decl.symbol] = decl
    return m


def fusion_contraints(template, var_types):
    """
    :returns: fusion constraints (i.e. last three asserts from filled template)
    """
    arity = get_z_idx(template)
    if "Int" in var_types or "Real" in var_types:
        return template.commands[-(arity + 1):]
    return template.commands[-(arity + 1):-arity]


def add_fusion_constraints(formula, asserts):
    """
    Add fusion constraint asserts to formula (after all other asserts)
    """
    last_ass_idx = get_last_assert_idx(formula)
    formula.commands = (
        formula.commands[: last_ass_idx + 1]
        + asserts
        + formula.commands[last_ass_idx + 1:]
    )


def add_var_decls(formula, declare_funs):
    """
    Add additional variable declarations to the formula (right before the first
    assert statement)
    """
    first_ass_idx = get_first_assert_idx(formula)
    formula.commands = (
        formula.commands[:first_ass_idx]
        + declare_funs
        + formula.commands[first_ass_idx:]
    )


def canonicalize_script(script):
    """
    Ensure that all variables will be declared before the first assert
    statement.
    """
    first_ass_idx = get_first_assert_idx(script)
    n_commands = len(script.commands)
    new_commands = []
    decls_after_ass = []
    for idx in range(n_commands):
        cmd = script.commands[idx]
        if idx > first_ass_idx\
           and isinstance(cmd, DeclareFun) or isinstance(cmd, DeclareConst):
            decls_after_ass.append(cmd)
        else:
            new_commands.append(cmd)
    script.commands = new_commands
    add_var_decls(script, decls_after_ass)
    return script
