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
    parse_sexpr,
    type2ffg,
)
from yinyang.src.parsing.Parse import parse_str
from yinyang.src.parsing.Ast import (
    Term,
    Script,
    Assert,
    DeclareConst,
    DeclareFun,
    DefineConst,
    DefineFun,
    DefineFunRec,
    DefineFunsRec,
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


def fusion_vars(script):
    """
    :returns: the global variables of script that can be fused, i.e. the
              declared constants (not functions or defined symbols), with
              their types
    """
    constants = {cmd.symbol for cmd in script.commands if is_constant(cmd)}
    return {
        var: typ for var, typ in script.global_vars.items()
        if var in constants
    }


def fused_name(names):
    """
    :returns: the name of the variable fusing the variables names, e.g.
              scr1_x_scr2_y_fused, quoted if a name is quoted:
              |scr1_x y_scr2_z_fused|
    """
    parts = [
        name[1:-1] if len(name) > 1 and name[0] == name[-1] == "|" else name
        for name in names
    ]
    name = "_".join(parts + ["fused"])
    return "|" + name + "|" if parts != list(names) else name


DECLARATION_COMMANDS = (
    "declare-sort", "define-sort", "declare-datatype", "declare-datatypes",
)


def is_declaration(cmd):
    """
    Checks whether cmd declares or defines sorts or symbols.
    """
    if isinstance(cmd, (DeclareConst, DeclareFun, DefineConst, DefineFun,
                        DefineFunRec, DefineFunsRec)):
        return True
    return isinstance(cmd, SMTLIBCommand) and \
        cmd.cmd_str.lstrip("( \t\n").startswith(DECLARATION_COMMANDS)


def declared_sorts(script):
    """
    :returns: dict mapping the sorts declared by declare-sort, define-sort,
              declare-datatype and declare-datatypes to the text of their
              declaration
    """
    sorts = {}
    for cmd in script.commands:
        if not (isinstance(cmd, SMTLIBCommand) and is_declaration(cmd)):
            continue
        text = " ".join(cmd.cmd_str.split())
        try:
            tree = parse_sexpr(text)
        except ValueError:
            continue
        if tree[0] == "declare-datatypes" and len(tree) > 1:
            names = [dec[0] for dec in tree[1] if isinstance(dec, list)]
        else:
            names = tree[1:2]
        for name in names:
            sorts[name] = text
    return sorts


def sort_clash(script1, script2):
    """
    Checks whether the scripts declare a sort or datatype with the same name
    but different declarations. Sorts are not renamed by
    Script.prefix_vars, so such scripts cannot be fused.
    """
    sorts1, sorts2 = declared_sorts(script1), declared_sorts(script2)
    return any(
        name in sorts2 and sorts2[name] != text
        for name, text in sorts1.items()
    )


def is_header(cmd):
    return isinstance(cmd, SMTLIBCommand) and \
        cmd.cmd_str.lstrip("( \t\n").startswith(("set-info", "set-option"))


def concat(op, script1, script2):
    """
    Combine two scripts with disjoint symbols (see Script.prefix_vars):
    the leading set-info/set-option commands of script2, the declarations
    and definitions of script1, then the commands of script2 with the
    asserts of both scripts combined by op in place of its assert. The
    combined assert comes after the last declaration of script2, as
    definitions may follow the first assert of a script. Sort and datatype
    declarations that occur in both scripts are kept once.
    """
    script1.merge_asserts()
    script2.merge_asserts()
    assert1 = [cmd for cmd in script1.commands if isinstance(cmd, Assert)][0]
    assert2 = [cmd for cmd in script2.commands if isinstance(cmd, Assert)][0]
    combined = Assert(Term(op=op, subterms=[assert1.term, assert2.term]))

    n_header = 0
    while n_header < len(script2.commands) and \
            is_header(script2.commands[n_header]):
        n_header += 1
    new_cmds = script2.commands[:n_header]
    declared = set()

    def add(cmd):
        if isinstance(cmd, SMTLIBCommand):
            text = " ".join(cmd.cmd_str.split())
            if text in declared:
                return
            declared.add(text)
        new_cmds.append(cmd)

    for cmd in script1.commands:
        if is_declaration(cmd):
            add(cmd)
    rest = [
        cmd for cmd in script2.commands[n_header:]
        if not isinstance(cmd, Assert)
    ]
    first_assert = next(
        i for i, cmd in enumerate(script2.commands[n_header:])
        if isinstance(cmd, Assert)
    )
    last_decl = max(
        [i + 1 for i, cmd in enumerate(rest) if is_declaration(cmd)],
        default=0,
    )
    rest.insert(max(first_assert, last_decl), combined)
    for cmd in rest:
        if is_declaration(cmd):
            add(cmd)
        else:
            new_cmds.append(cmd)
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
    type_var_maps = [copy.deepcopy(m1), copy.deepcopy(m2)]
    mapping = []

    def _random_couples(template):
        template_var_by_sort = get_variables_by_sort(template)
        arity = get_z_idx(template)
        maps = copy.deepcopy(type_var_maps)
        map_index = 0
        map_length = len(maps)
        vars = [0] * map_length
        output = [{} for i in range(map_length)]
        # Create a map from sorts of the template to variables.
        for sort in template_var_by_sort:
            random.shuffle(template_var_by_sort[sort])
            for template_var in template_var_by_sort[sort]:
                starting = map_index
                while True:
                    # Ensure at each iteration to change the map from
                    # where we pick, to try to equally distribute the
                    # variables in the seed formulas.
                    map_index = (map_index + 1) % map_length
                    # We need at least a variable to be available 
                    # for allocation
                    if (sort in maps[map_index] 
                            and len(maps[map_index][sort]) > 0):
                        break
                    if starting == map_index:
                        # This template cannot be instantiated with
                        # those seeds.
                        return
                vars[map_index] += 1
                var = random.choice(maps[map_index][sort])
                maps[map_index][sort].remove(var)
                output[map_index][var] = template_var
        if sum(vars) == arity:
            mapping.append((output[0], output[1], template))

    for sort_index in templates:
        for template in templates[sort_index]:
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
    # TODO Solve BitVec problem with a best effort approach:
    # try to generate formulas until you get the right bitvector type.
    templates = {}
    options1 = _map_to_ffg_theories(global_vars1)
    options2 = _map_to_ffg_theories(global_vars2)
    for op1 in options1:
        for op2 in options2:
            theories = [op1, op2]
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


def _map_to_ffg_theories(global_vars):
    """
    Filter only theories supported by ffg and maps them
    to options for it to be used in generate_tree.
    """
    ts = _type_list(global_vars)
    options = [type2ffg(ts[t]) for t in ts]
    options = list(filter(lambda t: t is not None, options))
    return options
