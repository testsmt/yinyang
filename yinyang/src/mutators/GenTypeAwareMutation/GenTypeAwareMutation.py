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

from yinyang.src.mutators.Mutator import Mutator
from yinyang.src.mutators.GenTypeAwareMutation.Operator import (
    Operator, handle_parametric_op, handle_non_parametric_op
)
from yinyang.src.mutators.GenTypeAwareMutation.Util import (
    get_all_subterms, binder_types, defines_names, free_symbols,
    visible_symbols
)
from yinyang.src.parsing.Ast import Const, Expr
from yinyang.src.parsing.Types import ALL


class GenTypeAwareMutation(Mutator):
    def __init__(self, formula, args, unique_expr):
        self.args = args
        self.formula = formula
        self.unique_expr = unique_expr
        self.operators = []
        self.parse_config_file()
        self.visible, self.declared = visible_symbols(formula.commands)
        self.free = {}  # id(term) -> scope information of unique_expr terms
        self.scope = None  # see set_scope
        self.choices = {}  # type -> terms that can be placed at the hole

    def set_scope(self, hole):
        """
        Restrict the terms used for replacing hole to those that are well
        scoped at the position of hole, see in_scope.
        """
        root = hole
        while root.parent is not None:
            root = root.parent
        self.scope = (
            binder_types(hole),
            self.visible.get(id(root), self.declared),
        )
        self.choices = {}

    def in_scope(self, term):
        """
        term: term object from unique_expr

        A term can be placed at the hole (see set_scope) if each of its
        free variables is
        (1) bound at the hole by a quantifier or let with the same type, or
        (2) a global symbol (declared in the formula, not bound in the
            context of term) that is declared before the assert of the hole
            and not shadowed at the hole,
        and each declared function it applies is declared before the
        assert of the hole and not shadowed at the hole. Terms with :named
        attributes are never used, as their copies would define the names
        a second time.
        """
        env, visible = self.scope
        if id(term) not in self.free:
            self.free[id(term)] = (
                free_symbols(term) + (binder_types(term),)
                if not defines_names(term) else None
            )
        if self.free[id(term)] is None:
            return False
        variables, functions, term_env = self.free[id(term)]
        for name, typ in variables.items():
            if name in env:
                if env[name] != typ:
                    return False
            elif name in term_env:
                return False  # bound in the context of term only
            elif name in self.declared and name not in visible:
                return False
        for name in functions:
            if name in env or (name in self.declared and
                               name not in visible):
                return False
        return True

    def get_choices(self, typ):
        """
        :returns: the terms of type typ that can be placed at the hole
        """
        if typ not in self.choices:
            self.choices[typ] = [
                term for term in self.unique_expr.get(typ, [])
                if self.scope is None or self.in_scope(term)
            ]
        return self.choices[typ]

    def parse_config_file(self):
        """
        Read the customizable configuration file.
        Customize the configuration file at yinyang/config/generalization.txt.
        Configuration file contains all the signatures of SMT-LIB operators
        and the signatures are used for operator choice during the mutation.
        """
        with open(self.args.config) as f:
            lines = f.readlines()

        for line in lines:
            line = line.strip("\n")  # remove linebreaks
            if ";" in line:  # ignore comments
                line = line[: line.index(";")]
            if line.strip() == "":  # skip empty lines
                continue
            line = line.strip()  # remove trailing whitespaces
            tokens = line.split(" ")

            if "par" not in tokens[0]:
                op_name, type_strings, attributes =\
                    handle_non_parametric_op(tokens)
                op = Operator(op_name, type_strings, attributes)
            else:
                op_name, type_strings, attributes, parameters =\
                    handle_parametric_op(tokens)
                op = Operator(op_name, type_strings, attributes, parameters)
            self.operators.append(op)

    def has_types(self, types):
        """
        types: list of types (possibly redundant)

        :returns: True if the seed formula supports the types
        """
        for t in set(types):
            if t == ALL:
                continue
            if not self.get_choices(t):
                return False
        return True

    def get_candidate_ops(self, term):
        """
        term: term object

        An operator op is a candidate (op arg1 ... argk ret)
        (1) if its return type matches the type of t or has polymorphic return
            type (i.e. ret == ALL) and
        (2) if the seed formula has terms t1...tn such that tk.type = argk.type

        :returns: a list of candidate operators
        """
        candidate_ops = []
        for op in self.operators:
            if op.rtype != ALL and op.rtype != term.type:
                continue
            if self.has_types(op.arg_types):
                candidate_ops.append(op)
        return candidate_ops

    def get_replacee(self, term):
        """
        term: term object

        Choose randomly an operator from the list of candidate operators.

        When id is chosen for the operator, we pick an expression of a
        same type as input term. Else, we choose expression(s) according to
        the signature of the operator from the configuration file and generate
        a new expression.

        :returns: newly generated expression for substitution
        """
        self.set_scope(term)
        candidate_ops = self.get_candidate_ops(term)

        if len(candidate_ops) == 0:
            return None

        op = random.choice(candidate_ops)
        args = []
        if op.name == "id":
            choices = [
                termPrime
                for termPrime in self.get_choices(term.type)
                if termPrime != term
            ]

            if len(choices) == 0:
                return None

            return random.choice(choices)
        else:
            for t in op.arg_types:
                choices = self.get_choices(t)

                if len(choices) == 0:
                    return None

                arg = random.choice(choices)
                args.append(arg)

            if len(op.arg_types) == 0:
                # Nullary operators (e.g. re.none, re.all, re.allchar) are
                # constants, not function applications, and must not be
                # printed with parentheses around them.
                return Const(name=op.name, type=op.rtype)

            # Expr makes the arguments point to exp; they are terms of
            # unique_expr, whose parents are needed for their scope.
            parents = [arg.parent for arg in args]
            exp = Expr(op=op.name, subterms=args)
            exp.type = op.rtype
            for arg, parent in zip(args, parents):
                arg.parent = parent

            return exp
        return None

    def mutate(self):
        """
        Perform a generative type-aware mutation.
        In case generator could not generate valid mutant, return false.

        :returns: mutant formula, and result of mutation
        """
        success = False
        self.av_expr, self.expr_type = get_all_subterms(self.formula)
        num_holes = len(self.av_expr)
        all_holes = self.av_expr
        for _ in range(num_holes):
            t1 = random.choice(all_holes)
            t2 = self.get_replacee(t1)
            if t2:
                success = True
                t1.substitute(t1, t2)
                break
            all_holes.remove(t1)
        return self.formula, success, False  # False = never skip seed
