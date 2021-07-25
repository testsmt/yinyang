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

from src.mutators.Mutator import Mutator
from src.mutators.SemanticFusion.VariableFusion import (
    fill_template,
    inv_x,
    inv_y,
    fusion_contraints,
    add_fusion_constraints,
    add_var_decls,
)
from src.mutators.SemanticFusion.Util import (
    random_var_triplets,
    disjunction,
    conjunction,
)
from src.base.Exitcodes import ERR_USAGE
from src.parsing.Parse import parse_str
from src.parsing.Ast import DeclareFun


class SemanticFusion(Mutator):
    def __init__(self, formula1, formula2, args):
        self.formula1 = formula1
        self.formula2 = formula2
        self.args = args
        self.config = self.args.config
        self.oracle = self.args.oracle
        self.templates = {}
        self._parse_mrs()

        if not self.oracle:
            print("error: No oracle {sat,unsat} specified")
            exit(ERR_USAGE)

    def _parse_mrs(self):
        with open(self.config) as f:
            lines = f.readlines()
        started = False
        curr = []
        _mrs = []

        for line in lines:
            if ";" in line:
                continue
            if not line.strip():
                continue
            if "begin" in line:
                started = True
                continue
            if "end" in line:
                started = False
                _mrs.append("\n".join(curr))
                curr = []
                continue
            if started:
                curr.append(line)

        for i, mr in enumerate(_mrs):
            template, _ = parse_str(mr)
            sort = template.commands[0].sort

            if sort not in self.templates:
                self.templates[sort] = [template]
            else:
                self.templates[sort].append(template)

    def fuse(self, formula1, formula2, triplets):

        fusion_vars = []
        fusion_constr = []
        for triplet in triplets:
            x, y, template, var_type =\
                triplet[0], triplet[1], triplet[2], triplet[3]
            z = DeclareFun(x + "_" + y + "_fused", "", var_type)
            fusion_vars.append(z)
            template = fill_template(x, y, template, var_type)
            fusion_constr += fusion_contraints(template, var_type)

            occs_x = [occ for occ in formula1.free_var_occs if occ.name == x]
            occs_y = [occ for occ in formula2.free_var_occs if occ.name == y]

            k = random.randint(0, len(occs_x))
            occs_x = random.sample(occs_x, k)
            k = random.randint(0, len(occs_y))
            occs_y = random.sample(occs_y, k)

            for occ in occs_x:
                occ.substitute(occ, inv_x(template))
            for occ in occs_y:
                occ.substitute(occ, inv_y(template))

        if self.oracle == "unsat":
            formula = disjunction(formula1, formula2)
            add_fusion_constraints(formula, fusion_constr)
        else:
            formula = conjunction(formula1, formula2)
        add_var_decls(formula, fusion_vars)

        return formula

    def mutate(self):
        skip_seed = False
        if self.formula1.free_var_occs == [] and\
           self.formula2.free_var_occs == []:
            skip_seed = True

        formula1, formula2 =\
            copy.deepcopy(self.formula1), copy.deepcopy(self.formula2)
        formula1.prefix_vars("scr1_")
        formula2.prefix_vars("scr2_")

        triplets = random_var_triplets(
            formula1.global_vars, formula2.global_vars, self.templates
        )
        fused = self.fuse(formula1, formula2, triplets)
        return fused, True, skip_seed
