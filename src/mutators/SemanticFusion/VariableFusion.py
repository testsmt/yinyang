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
import string

from src.parsing.Ast import Const, Var, Expr, Assert, DeclareConst


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


def fill_template(x, y, template, var_type):
    """
    Binds the variable name to the template.
    :x: variable name of first formula
    :y: variable name of second formula
    :returns: bindded template
    """
    filled_template = copy.deepcopy(template)
    first_ass_idx = get_first_assert_idx(filled_template)
    z = Var(x + "_" + y + "_fused", var_type)

    # Detect whether template includes random variable c
    random_constant_idx = get_constant_idx(template)
    if random_constant_idx != -1:
        declare_const = template.commands[random_constant_idx]
        const_type = declare_const.sort
        const_expr = get_constant_value(declare_const)

        for ass in filled_template.commands[first_ass_idx:]:
            ass.term.substitute(Var("c", const_type), const_expr)

    # Bind occurrences x,y to template
    for ass in filled_template.commands[first_ass_idx:]:
        ass.term.substitute(Var("z", z.type), z)
        ass.term.substitute(Var("x", var_type), Var(x, var_type))
        ass.term.substitute(Var("y", var_type), Var(y, var_type))

    return filled_template


def inv_x(template):
    """
    :returns: inversion function term for variable occurrence x
    """
    if get_constant_idx(template) != -1:
        return template.commands[5].term.subterms[1]

    return template.commands[4].term.subterms[1]


def inv_y(template):
    """
    :returns: inversion function term for variable occurrence y
    """
    if get_constant_idx(template) != -1:
        return template.commands[6].term.subterms[1]

    return template.commands[5].term.subterms[1]


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
