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

import random
import copy
import re
import string

from yinyang.src.parsing.Ast import (
    Const, Var, Expr, Assert, DeclareConst, DeclareFun, Script
)
from yinyang.src.parsing.Types import BITVECTOR_TYPE


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
        if constant_name_pattern.match(decl.symbol) != None:
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
        if isinstance(decl, DeclareConst) and constant_name_pattern.match(decl.symbol) != None:
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

    if const_type == "Int":
        r = random.randint(-1000, 1000)
        if r < 0:
            return Expr(op="-",
                        subterms=[Const(name=str(-r), type=const_type)])
        else:
            return Const(name=str(r), type=const_type)

    if const_type == "Real":
        r = round(random.uniform(-1000, 1000), 5)
        if r < 0:
            return Expr(op="-",
                        subterms=[Const(name=str(-r), type=const_type)])
        else:
            return Const(str(r), type=const_type)

    if const_type == "Bool":
        return Const(random.choice(["true", "false"]), type=const_type)

    if const_type == "String":
        length = random.randint(0, 20)
        return Const('"' + gen_random_string(length) + '"', type=const_type)

    if isinstance(const_type, BITVECTOR_TYPE):
        length = const_type.bitwidth
        return Const(f"#b{random.getrandbits(length):0{length}b}", type=const_type)


def fill_template(x, y, template):
    """
    Binds the variable name to the template.
    :x: variable name of first formula
    :y: variable name of second formula
    :returns: bindded template
    """
    filled_template = copy.deepcopy(template)
    first_ass_idx = get_first_assert_idx(filled_template)
    z = Var(x + "_" + y + "_fused", z_sort(template))

    # Detect whether template includes random variable c
    first_random_constant_idx = get_first_constant_idx(template)
    if first_random_constant_idx != -1:
        last_random_constant_idx = get_last_constant_idx(template)
        assert first_ass_idx == last_random_constant_idx + 1
        for i in range(first_random_constant_idx, last_random_constant_idx + 1):
            declare_const = template.commands[i]
            const_type = declare_const.sort
            const_expr = get_constant_value(declare_const)

            for ass in filled_template.commands[first_ass_idx:]:
                ass.term.substitute(
                    Var(declare_const.symbol, const_type), const_expr)

    # Bind occurrences x,y to template
    for ass in filled_template.commands[first_ass_idx:]:
        ass.term.substitute(Var("z", z.type), z)
        ass.term.substitute(Var("x", x_sort(template)),
                            Var(x, x_sort(template)))
        ass.term.substitute(Var("y", y_sort(template)),
                            Var(y, y_sort(template)))

    return filled_template


def x_sort(template):
    """
    returns: returns the sort of variable x
    """
    if template.commands[0].symbol != 'x':
        ValueError(
            'Expected x variable declaration as first command in the fusion function.')
    return template.commands[0].sort


def y_sort(template):
    """
    returns: returns the sort of variable x
    """
    if template.commands[1].symbol != 'y':
        ValueError(
            'Expected y variable declaration as first command in the fusion function.')
    return template.commands[1].sort


def z_sort(template):
    """
    returns: returns the sort of variable x
    """
    if template.commands[2].symbol != 'z':
        ValueError(
            'Expected z variable declaration as first command in the fusion function.')
    return template.commands[2].sort


def inv_x(template):
    """
    :returns: inversion function term for variable occurrence x
    """
    return template.commands[-2].term.subterms[1]


def inv_y(template):
    """
    :returns: inversion function term for variable occurrence y
    """
    return template.commands[-1].term.subterms[1]


def fusion_contraints(template, var_type):
    """
    :returns: fusion constraints (i.e. last three asserts from filled template)
    """
    if var_type == "Int" or var_type == "Real":
        return template.commands[-3:]
    return template.commands[-3:-2]


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
