import random

from src.generators.SemanticFusion.Symbol import Symbol, Symbols, MetamorphicTuple

def get_script_from_file(file):
    with open(file,"r") as reader:
        script = reader.read()
    return script

def clean_bv(string):
    string = string.replace("BV{","(_ BitVec ")
    string = string.replace("}",")")
    return string

def unsupported_file(fname):
    with open(fname) as fp:
        for i in range(0,4):
            line = fp.readline()
        if "Constructed by Trevor Hansen to test edge case parsing" in line:
            return True

def get_num_variables(fname):
    with open(fname) as fp:
        data = fp.readlines()
        count = "".join(data).count("declare-fun")
    return count

def string2file(fn, string):
    with open(fn, "w") as f: f.write(string)

def warning_or_error(stdout, stderr):
    stdstream = stdout + " " + stderr
    if "model is not available" in stdstream or "Cannot get model" in stdstream: return False
    return "LEAKED" in stdstream or \
           "Leaked" in stdstream or \
           "Segmentation fault" in stdstream or \
           "segmentation fault" in stdstream or \
           "segfault" in stdstream or \
           "ASSERTION VIOLATION" in stdstream or \
           "(error" in stdstream or \
           "Assertion failure" in stdstream or \
           "Fatal failure" in stdstream or \
           "Internal error detected" in stdstream or \
           "an invalid model was generated" in stdstream or \
           "Failed to verify" in stdstream or \
           "failed to verify" in stdstream or \
           "ERROR: AddressSanitizer:" in stdstream


def get_commands(script):
    commands = []
    bracket_counter = -1
    bracket_content = ""
    in_quote = False
    for c in script:
        if c == '"':
            in_quote = not in_quote
        if not in_quote:
            if c == '(':
                if bracket_counter > 0:
                    bracket_counter += 1
                elif bracket_counter == -1:
                    bracket_counter = 1
                else:
                    print("invalid formula")
                    exit(1)
            elif c == ")":
                bracket_counter -= 1
                if bracket_counter == 0:
                    commands.append(bracket_content+")")
                    bracket_content = ""
                    bracket_counter = -1
        if bracket_counter != -1: bracket_content += c
    return commands

def decompose(script):
    commands = get_commands(script)
    logic = [c for c in commands if c.startswith("(set-logic")]
    if len(logic) > 0:
        logic = logic[0]
    else:
        logic = []
    decl_consts = [c for c in commands if c.startswith("(declare-const")]
    decl_funcs = [c for c in commands if c.startswith("(declare-fun")]
    def_funcs = [c for c in commands if c.startswith("(define-fun")]
    def_sorts= [c for c in commands if c.startswith("(declare-sort")]
    asserts = [c for c in commands if c.startswith("(assert")]
    return "".join(logic), list(def_sorts), list(decl_consts),\
          list(decl_funcs), list(def_funcs), list(asserts)

def get_symbol(declaration):
    #get symbol
    prefix = declaration.split(" ")[0]
    symbol = ""
    index = declaration.find(prefix)+len(prefix)
    while declaration[index] == " " or declaration[index] == "\n":
        index += 1
    if declaration[index] == "|":
        bracket_counter = 1
        while bracket_counter != 0:
            index += 1
            if declaration[index] == "|":  bracket_counter -= 1
            elif bracket_counter != 0:
                symbol = symbol + declaration[index]
        symbol = "|%s|" %symbol
    else:
        while declaration[index] != " " and declaration[index] != "\n":
            symbol = symbol + declaration[index]
            index += 1

    index = declaration.find(symbol)+len(symbol)
    s_type = ""

    while declaration[index] == " ":
        index += 1
    if declaration[index] == "(":
        bracket_counter = 1
        while bracket_counter != 0:
            index += 1
            if declaration[index] == "(":  bracket_counter += 1
            elif declaration[index] == ")": bracket_counter -= 1
    if declaration[index] == ")": index += 1

    while declaration[index] == " ":
        index += 1
    if declaration[index] == "(":
        bracket_counter = 1
        while bracket_counter != 0:
            index += 1
            if declaration[index] == "(":
                bracket_counter += 1
            elif declaration[index] == ")":
                bracket_counter -= 1
            s_type = s_type + declaration[index]
        s_type = "(%s" %s_type
    else:
        while declaration[index] != " " and declaration[index] != "\n" and declaration[index] != ")":
            s_type = s_type + declaration[index]
            index += 1

    # #get type
    # index = -2
    # s_type = ""
    # while declaration[index] == " ":
    #     index -= 1
    # if declaration[index] == ")":
    #     bracket_counter = 1
    #     while bracket_counter != 0:
    #         index -= 1
    #         if declaration[index] == ")":  bracket_counter += 1
    #         elif declaration[index] == "(": bracket_counter -= 1
    #         if bracket_counter != 0:
    #             s_type = declaration[index] + s_type
    #     s_type = "(%s)" %s_type
    # else:
    #     while declaration[index] != " ":
    #         s_type = declaration[index] + s_type
    #         index -= 1
#    print(s_type)
    return Symbol(symbol, s_type)

def fun_has_arguments(line):
    if ("(declare-fun" in line or "(define-fun" in line) and not "()" in line:
        return True
    return False

def get_symbols(string, only_zero_valued_funcs=False):
    commands = get_commands(string)
    symbols = []
    declarations = [c for c in commands if c.startswith("(declare-const") or\
                    c.startswith("(declare-fun")\
                    or c.startswith("(define-fun")]

    for declaration in declarations:
        if fun_has_arguments(declaration): continue
        symbols.append(get_symbol(declaration))
    return Symbols(symbols)

def get_declared_symbols(string, only_zero_valued_funcs=False):
    commands = get_commands(string)
    symbols = []
    declarations = [c for c in commands if c.startswith("(declare-const") or\
                    c.startswith("(declare-fun")\
                    or c.startswith("(define-fun")]

    for declaration in declarations:
        symbols.append(get_symbol(declaration))
    return Symbols(symbols)

def disjunction(script1, script2):
    """
    Disjunction of two SMT scripts
    Assumption: script1 and script2 have no shared variables
    """
    _,decl_sorts1, decl_consts1, decl_funcs1, def_funcs1, asserts1 = decompose(script1)
    _,decl_sorts2, decl_consts2, decl_funcs2, def_funcs2, asserts2 = decompose(script2)
    sorts = list(set(decl_sorts1).union(set(decl_sorts2)))
    disjunction =  "".join(sorts) + "".join(decl_consts1) + "".join(decl_consts2)\
                  + "".join(decl_funcs1) + "".join(decl_funcs2) + "".join(def_funcs1) + "".join(def_funcs2)


    conjunction1 = " (and"
    random.shuffle(asserts1)
    for assertion in asserts1:
        assertion = assertion.strip("(assert")
        assertion = assertion[:assertion.rfind(")")]
        conjunction1 += assertion
    conjunction1 += ")"

    conjunction2 = " (and"
    random.shuffle(asserts2)
    for assertion in asserts2:
        assertion = assertion.strip("(assert")
        assertion = assertion[:assertion.rfind(")")]
        conjunction2 += assertion
    conjunction2 += ")"

    disjunction += "(assert (or %s %s))" %(conjunction1,conjunction2)
    return disjunction

def random_map(symbols1, symbols2):
    metamophic_tuples = []
    symbols2_type_list = []
    for symbol2 in symbols2.symbols:
        if symbol2.type not in symbols2_type_list:
            symbols2_type_list.append(symbol2.type)
    for symbol1 in symbols1.symbols:
        if symbol1.type not in symbols2_type_list:
            continue
        symbol2 = random.choice(symbols2.symbols)
        while symbol1.type != symbol2.type:
            symbol2 = random.choice(symbols2.symbols)
        metamophic_tuples.append(MetamorphicTuple(symbol1, symbol2))
    return metamophic_tuples

def ranking_map(symbol1, symbol2, script1, script2):
    metamophic_tuples = []
    sorted_symbols1 = []
    sorted_symbols2 = []
    for symbol in symbol1.symbols:
        symbol.set_occurrences(script1)
        sorted_symbols1.append(symbol)
    for symbol in symbol2.symbols:
        symbol.set_occurrences(script2)
        sorted_symbols2.append(symbol)
    sorted_symbols1.sort(key=get_occurrences)
    sorted_symbols2.sort(key=get_occurrences)
    for symbol1 in sorted_symbols1:
        for symbol2 in sorted_symbols2:
            if symbol1.type == symbol2.type:
                sorted_symbols2.remove(symbol2)
                metamophic_tuples.append(MetamorphicTuple(symbol1, symbol2))
                break
    return metamophic_tuples

def get_occurrences(symbol):
    return symbol.occurrences


def replace_variable(line, source, target, prob=100):
    if "((%s " % source in line:
        return line  # source is a quantifier
    l = []
    for token in line.split(" "):
        if token == source or token.startswith(source+")") or token.endswith("("+source):
            weighted_random = [True] * prob + [False] * (100 - prob)
            if random.choice(weighted_random):
                l.append(token.replace(source, target))
            else:
                l.append(token)
        else:
            l.append(token)
    return " ".join(l)


def shift_script(script, prefix):
    symbols = get_declared_symbols(script)
    var_map = symbols.get_shiftmap(prefix)
    script_text = script.split('\n')
    new_script_text = ""
    for line in script_text:
        new_line = line
        for var in var_map:
            new_line = replace_variable(new_line, var, var_map[var])
        if not new_line.startswith(";"):
            new_script_text = new_script_text + " " + new_line
    return new_script_text

