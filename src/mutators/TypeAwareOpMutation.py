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

from src.mutators.Mutator import Mutator


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
            arity = -1
            if ":arity" in line:
                arity = line.split(":arity")[-1].split(" ")[-1].strip()
                line = " ".join(line.split(" ")[:-2])
            if "->" in line:
                op_from = line.split("->")[0].strip()
                op_to = line.split("->")[1].strip()
                self.unidirectional.append((arity, op_from, op_to))
                continue

            op_class = [op.strip() for op in line.split(",")]
            self.bidirectional.append((arity, op_class))

    def arities_mismatch(self, arity, op_occ):
        if arity == "2+" and len(op_occ.subterms) < 2:
            return True

        if arity == "1-" and len(op_occ.subterms) > 2:
            return True
        return False

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
            arity, op, replacee = u[0], u[1], u[2]
            if op_occ.op != op or op_occ.quantifier != op:
                continue
            if self.arities_mismatch(arity, op_occ):
                continue
            return replacee
        return None

    def mutate(self):
        success = False
        for _ in range(self.args.modulo):
            max_choices = len(self.formula.op_occs)
            for _ in range(max_choices):
                op_occ = random.choice(self.formula.op_occs)
                replacee = self.get_replacee(op_occ)
                if replacee:
                    success = True
                    op_occ.op = replacee
                    break
        return self.formula, success, False
