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

from ffg.emitter.yinyang_emitter import emit_function
from ffg.gen.tree_generation import generate_tree
from ffg.gen import gen_configuration
from yinyang.src.parsing.Types import (
    ARRAY_TYPE,
    BITVECTOR_TYPE,
    FP_TYPE,
    type2ffg,
)
from yinyang.src.parsing.Parse import parse_str
from yinyang.src.parsing.Ast import (
    Term,
    Script,
    Assert,
    DeclareConst,
    DeclareFun,
    SMTLIBCommand,
)
from yinyang.src.mutators.SemanticFusion.VariableFusion import (
    get_variable_sort_by_idx,
    get_variables_by_sort,
    get_z_idx
)
import copy
import io
import random
import itertools


def cvars(occs):
    """
    Return a single representative occurrence for each variable.
    """
    names = []
    canonicals = []
    for occ in occs:
        if occ.name in names:
            continue
        canonicals.append(occ)
    return canonicals


def debug_formula(formula, name="formula"):
    print("#" * 10, name, "#" * 10)
    print(formula.__str__())
    print("#" * (10 + len(name) + 10))
    print()


def is_constant(cmd):
    if isinstance(cmd, DeclareConst):
        return True
    if isinstance(cmd, DeclareFun) and cmd.input_sort == "":
        return True
    return False


def is_sort(cmd):
    if isinstance(cmd, SMTLIBCommand) and "-sort" in cmd.cmd_str:
        return True
    return False


def concat(op, script1, script2):
    script1.merge_asserts()
    script2.merge_asserts()
    sorts = []
    sorts = [
        cmd for cmd in script1.commands + script2.commands if is_sort(cmd)
    ]
    sorts = list(set(sorts))
    declares1 = [cmd for cmd in script1.commands if is_constant(cmd)]
    assert1 = [cmd for cmd in script1.commands if isinstance(cmd, Assert)][0]
    assert2 = [cmd for cmd in script2.commands if isinstance(cmd, Assert)][0]
    conjunction = Assert(Term(op=op, subterms=[assert1.term, assert2.term]))
    new_cmds = declares1

    for cmd in script2.commands:
        if is_sort(cmd):
            continue
        if isinstance(cmd, Assert):
            new_cmds.append(conjunction)
        else:
            new_cmds.append(cmd)
    new_cmds = sorts + new_cmds
    return Script(new_cmds, {**script1.global_vars, **script2.global_vars})


def conjunction(script1, script2):
    return concat("and", script1, script2)


def disjunction(script1, script2):
    return concat("or", script1, script2)


def type_var_map(global_vars):
    mapping = {}
    for var in global_vars:
        if str(global_vars[var]) not in mapping:
            mapping[str(global_vars[var])] = [var]
        else:
            if var not in mapping[str(global_vars[var])]:
                mapping[str(global_vars[var])].append(var)
    return mapping


def random_tuple_list(lst1, lst2, lb=1):
    """
    Generate a random list of tuples (x,y) where x is in lst1 and y is in lst2;
    """
    product = list(itertools.product(lst1, lst2))

    if len(product) == 0:
        k = 0
    else:
        k = random.randint(lb, len(product))
    tups = random.sample(product, k)
    random.shuffle(tups)

    new_tups = []
    lhs, rhs = [], []
    for tup in tups:
        if tup[0] in lhs:
            continue
        if tup[1] in rhs:
            continue
        lhs.append(tup[0])
        rhs.append(tup[1])
        new_tups.append(tup)
    return new_tups


def random_var_triplets(global_vars1, global_vars2, templates):
    """
    Create a random variable mapping of variables with same type
    """
    m1, m2 = type_var_map(global_vars1), type_var_map(global_vars2)
    mapping = []

    def _random_couples(template):
        template_var_by_sort = get_variables_by_sort(template)
        arity = get_z_idx(template)
        vars = [0, 0]
        maps = [copy.deepcopy(m1), copy.deepcopy(m2)]
        output = [{}, {}]
        # Create a map from sorts of the template to variables.
        for sort in template_var_by_sort:
            for template_var in template_var_by_sort[sort]:
                map_index = random.choice([0, 1])
                if (sort not in maps[map_index]):
                    map_index = (map_index + 1) % 2
                if (sort not in maps[map_index]):
                    break
                vars[map_index] += 1
                var = random.choice(maps[map_index][sort])
                maps[map_index][sort].remove(var)
                output[map_index][var] = template_var
        if (len(output[0]) + len(output[1]) == len(arity) and
                not len(output[0]) == 0 and not len(output[1]) == 0):
            mapping.append((output[0], output[1], template))

    for template in templates:
        _random_couples(template)
    return mapping


def _type_list(global_vars):
    """
    Return a list of variable types that can be used to 
    generate new fusion functions.
    """
    mapping = {}
    for var in global_vars:
        if isinstance(global_vars[var], ARRAY_TYPE) or \
            isinstance(global_vars[var], FP_TYPE) or \
                isinstance(global_vars[var], BITVECTOR_TYPE):
            continue
        if str(global_vars[var]) not in mapping:
            mapping[str(global_vars[var])] = global_vars[var]
    return mapping


def populate_template_map(templates, template):
    """
    Given a template and a template map, insert this 
    template inside the map using as index the tuple
    containing the sorts of the input variables.
    Do nothing if the arity of the fusion function is
    different from the number of variables requested.
    """
    # Use the type information of x and y.
    arity = get_z_idx(template)
    sort = tuple(sorted([str(get_variable_sort_by_idx(template, i))
                         for i in range(arity)]))
    if sort not in templates:
        templates[sort] = [template]
    else:
        templates[sort].append(template)


def generate_fusion_function_templates(
        global_vars1,
        global_vars2,
        variables: int,
        size=25
):
    """
    Create random variables mapping of variables from the seeds
    and new fusion functions to fuse them. Returns the templates
    used to perform the fuse step.
    """
    # Solve BitVec problem with a best effort approach:
    # try to generate formulas until you get the right bitvector type.
    tlist1 = _type_list(global_vars1)
    tlist2 = _type_list(global_vars2)
    templates = {}

    for t1 in tlist1:
        type1 = tlist1[t1]
        for t2 in tlist2:
            type2 = tlist2[t2]
            theories = [type2ffg(type1), type2ffg(type2)]
            gen_configuration.set_available_theories(theories)
            operator_types = gen_configuration.get_theories()
            root_type = random.choice(operator_types)
            tree, _ = generate_tree(
                root_type, size, [f"x{i}" for i in range(variables)], 'z')
            output = io.StringIO()
            emit_function(tree, output, wrap=False)
            template, _ = parse_str(output.getvalue())
            populate_template_map(templates, template)

    return templates
