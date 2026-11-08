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
from yinyang.src.parsing.Cvc5 import cvc5_unsupported


class TypeAwareOpMutation(Mutator):
    def __init__(self, formula, args):
        self.args = args
        self.formula = formula
        self.bidirectional = []
        self.unidirectional = []

        self.parse_config_file()

    def parse_config_file(self):
        with open(self.args.config) as f:
            lines = f.readlines()

        for line in lines:
            if ";" in line:
                continue
            if not line.strip():
                continue
            arity = None
            if ":arity" in line:
                line, arity = line.split(":arity")
                arity = arity.strip()
            if "->" in line:
                op_from = line.split("->")[0].strip()
                ops_to = [op.strip() for op in line.split("->")[1].split(",")]
                self.unidirectional.append((arity, op_from, ops_to))
                continue

            op_class = [op.strip() for op in line.split(",")]
            self.bidirectional.append((arity, op_class))

    def arities_mismatch(self, arity, op_occ):
        """
        Checks whether the number of arguments of op_occ violates the arity
        condition of a mutation: "N" (exactly N), "N+" (at least N) or "N-"
        (at most N) arguments; None means any number of arguments.
        """
        if arity is None:
            return False
        n = len(op_occ.subterms) if op_occ.subterms else 0
        if arity.endswith("+"):
            return n < int(arity[:-1])
        if arity.endswith("-"):
            return n > int(arity[:-1])
        return n != int(arity)

    def get_replacee(self, op_occ):
        for b in self.bidirectional:
            arity, op_class = b[0], b[1]
            if self.arities_mismatch(arity, op_occ):
                continue

            if op_occ.op in op_class:
                diff = op_class.copy()
                diff.remove(op_occ.op)
                replacee = random.choice(diff)
                return replacee

            if op_occ.quantifier in op_class:
                diff = op_class.copy()
                diff.remove(op_occ.quantifier)
                replacee = random.choice(diff)
                return replacee

        for u in self.unidirectional:
            arity, op, replacees = u[0], u[1], u[2]
            if op_occ.op != op and op_occ.quantifier != op:
                continue
            if self.arities_mismatch(arity, op_occ):
                continue
            return random.choice(replacees)
        return None

    def mutate(self):
        success = False
        for _ in range(self.args.modulo):
            max_choices = len(self.formula.op_occs)
            for _ in range(max_choices):
                op_occ = random.choice(self.formula.op_occs)
                replacee = self.get_replacee(op_occ)
                if replacee:
                    old = (op_occ.op, op_occ.quantifier)
                    if op_occ.quantifier:
                        op_occ.quantifier = replacee
                    else:
                        op_occ.op = replacee
                    if getattr(self.args, "cvc5_compat", False) and \
                            cvc5_unsupported(self.formula):
                        # e.g. = -> distinct on the definition of a RegLan
                        # constant: undo and mutate elsewhere.
                        op_occ.op, op_occ.quantifier = old
                        continue
                    success = True
                    break
        return self.formula, success, False
