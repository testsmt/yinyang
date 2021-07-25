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

import copy


class Script:
    def __init__(self, commands, global_vars):
        self.commands = commands
        self.vars, self.types = self._decl_commands()
        self.global_vars = global_vars
        self.free_var_occs = []
        self.op_occs = []
        self.assert_cmd = []

        for cmd in self.commands:
            if isinstance(cmd, Assert):
                globs_ = copy.deepcopy(self.global_vars)
                self._get_free_var_occs(cmd.term, self.global_vars)
                self.global_vars = globs_
                self._get_op_occs(cmd.term)
                self.assert_cmd.append(cmd)

    def _get_op_occs(self, e):
        if isinstance(e, str):
            return
        if e.is_const:
            return
        if e.label:
            return
        if e.is_var:
            return

        self.op_occs.append(e)
        for sub in e.subterms:
            self._get_op_occs(sub)

    def _get_free_var_occs(self, e, global_vars):
        if isinstance(e, str):
            return
        if e.is_const:
            return
        if e.label:
            return
        if e.quantifier:
            for var in list(global_vars):
                for quantified_var in e.quantified_vars:
                    if var == quantified_var[0]:
                        global_vars.pop(var)

        if e.var_binders:
            for var in list(global_vars):
                for let_var in e.var_binders:
                    if var == let_var:
                        global_vars.pop(var)
            for let_term in e.let_terms:
                self._get_free_var_occs(let_term, global_vars)

        if e.is_var:
            if e.name in global_vars:
                self.free_var_occs.append(e)
            return

        for sub in e.subterms:
            self._get_free_var_occs(sub, global_vars)

    def _decl_commands(self):
        vars, types = [], {}
        for cmd in self.commands:
            if isinstance(cmd, DeclareConst):
                vars.append(Var(cmd.symbol, cmd.sort))
                types[cmd.symbol] = cmd.sort
            if isinstance(cmd, DeclareFun):
                if cmd.input_sort != "":
                    vars.append(Var(cmd.symbol, cmd.input_sort))
                    types[cmd.symbol] = cmd.input_sort
        return vars, types

    def _prefix_free_vars(self, prefix, e):
        if isinstance(e, str):
            return
        if e.is_const:
            return
        if e.is_var and e.type:
            if e in self.free_var_occs:
                e.name = prefix + e.name
            return

        if e.var_binders:
            for i, var in enumerate(e.var_binders):
                self._prefix_free_vars(prefix, e.let_terms[i])

        for s in e.subterms:
            self._prefix_free_vars(prefix, s)

    def prefix_vars(self, prefix):
        """
        Add a shared prefix to all variables
        :prefix: str
        """
        for cmd in self.commands:
            if isinstance(cmd, DeclareConst):
                cmd.symbol = prefix + cmd.symbol
            if isinstance(cmd, DeclareFun):
                if cmd.input_sort == "":
                    cmd.symbol = prefix + cmd.symbol
            if isinstance(cmd, Assert):
                self._prefix_free_vars(prefix, cmd.term)
        new_global_vars = {}
        for global_var in self.global_vars:
            new_global_vars[prefix + global_var] = self.global_vars[global_var]
        self.global_vars = new_global_vars
        self.vars, self.types = self._decl_commands()

    def merge_asserts(self):
        """
        Merge all assert blocks (possibly separated by exit, reset,
        reset-assertions statement) into a single assert by conjunction.
        """
        terms = []
        for cmd in self.commands:
            if isinstance(cmd, Assert):
                terms.append(cmd.term)
            if isinstance(cmd, SMTLIBCommand):
                if cmd.cmd_str == "(exit)":
                    break
                if cmd.cmd_str == "(reset)":
                    terms = []
                if cmd.cmd_str == "(reset-assertions)":
                    terms = []
        conjunction = Assert(Term(op="and", subterms=terms))
        new_cmds, first_found = [], False
        for cmd in self.commands:
            if not first_found and isinstance(cmd, Assert):
                new_cmds.append(conjunction)
                first_found = True
            if isinstance(cmd, Assert):
                continue
            if isinstance(cmd, SMTLIBCommand):
                if cmd.cmd_str == "(exit)":
                    break
                if cmd.cmd_str == "(reset-assertions)":
                    continue
                if cmd.cmd_str == "(reset)":
                    new_cmds, first_found = [], False
                    continue
            new_cmds.append(cmd)
        self.commands = new_cmds

    def __str__(self):
        s = ""
        for i, c in enumerate(self.commands):
            if i != len(self.commands) - 1:
                s += c.__str__() + "\n"
            else:
                s += c.__str__()
        return s


class Commands:
    def __init__(self):
        self.free_vars = []


class DeclareConst(Commands):
    def __init__(self, symbol, sort):
        self.symbol = symbol
        self.sort = sort

    def __str__(self):
        return "(declare-const "\
               + self.symbol + " "\
               + self.sort.__str__() + ")"


class DeclareFun:
    def __init__(self, symbol, input_sort, output_sort):
        self.symbol = symbol
        self.input_sort = input_sort
        self.output_sort = output_sort

    def __str__(self):
        return (
            "(declare-fun "
            + self.symbol
            + " ("
            + self.input_sort
            + ") "
            + self.output_sort
            + ")"
        )


class Assert:
    def __init__(self, term):
        self.term = term

    def __str__(self):
        return "(assert " + self.term.__str__() + ")"


class AssertSoft:
    def __init__(self, term, attr):
        self.term = term
        self.attr = attr

    def __str__(self):
        for a in self.attr:
            attr_s = " " + a[0] + " " + a[1]
        return "(assert-soft " + self.term.__str__() + attr_s + ")"


class Comment:
    def __init__(self, txt):
        self.txt = txt

    def __str__(self):
        return "; " + self.txt


class Define:
    def __init__(self, symbol, term):
        self.term = term
        self.symbol = symbol

    def __str__(self):
        return "(define " + self.symbol + " " + self.term.__str__() + ")"


class DefineConst:
    def __init__(self, symbol, sort, term):
        self.symbol = symbol
        self.sort = sort
        self.term = term

    def __str__(self):
        return (
            "(define-const "
            + self.symbol
            + " "
            + self.sort
            + " "
            + self.term.__str__()
            + ")"
        )


class DefineFun:
    def __init__(self, symbol, sorted_vars, sort, term):
        self.symbol = symbol
        self.sorted_vars = sorted_vars
        self.sort = sort
        self.term = term

    def __str__(self):
        return (
            "(define-fun "
            + self.symbol
            + " ("
            + self.sorted_vars
            + ") "
            + self.sort
            + " "
            + self.term.__str__()
            + ")"
        )


class DefineFunRec:
    def __init__(self, symbol, sorted_vars, sort, term):
        self.symbol = symbol
        self.sorted_vars = sorted_vars
        self.sort = sort
        self.term = term

    def __str__(self):
        s = ""
        if len(self.sorted_vars) > 0:
            s = self.sorted_vars[0]
            for var in self.sorted_vars[1:]:
                s += " " + var
        return (
            "(define-fun-rec "
            + self.symbol
            + " ("
            + s
            + ") "
            + self.sort
            + " "
            + self.term.__str__()
            + ")"
        )


class FunDecl:
    def __init__(self, symbol, sorted_vars, sort):
        self.symbol = symbol
        self.sorted_vars = sorted_vars
        self.sort = sort

    def __str__(self):
        s = self.sorted_vars[0]
        for svar in self.sorted_vars[1:]:
            s += " " + svar
        return "(" + self.symbol + " (" + s + ") " + self.sort + ")"


class DefineFunsRec:
    def __init__(self, fun_decls, terms):
        self.fun_decls = fun_decls
        self.terms = terms

    def __str__(self):
        s = "(define-funs-rec (" + self.fun_decls[0].__str__()
        if len(self.fun_decls) > 1:
            for decl in self.fun_decls[1:]:
                s += " " + decl.__str__()
            s += ") (" + self.terms[0].__str__()
        if len(self.terms) > 1:
            for term in self.terms[1:]:
                s += " " + term.__str__()
            s += ")"
        return s + ")"


class Simplify:
    def __init__(self, term, attr):
        self.term = term
        self.attr = attr

    def __str__(self):
        attr_s = ""
        for a in self.attr:
            attr_s = " " + a[0] + " " + a[1]
        return "(simplify " + self.term.__str__() + attr_s + ")"


class Minimize:
    def __init__(self, term):
        self.term = term

    def __str__(self):
        return "(minimize " + self.term.__str__() + ")"


class Maximize:
    def __init__(self, term):
        self.term = term

    def __str__(self):
        return "(maximize " + self.term.__str__() + ")"


class Display:
    def __init__(self, term):
        self.term = term

    def __str__(self):
        return "(display" + self.term.__str__() + ")"


class Eval:
    def __init__(self, term):
        self.term = term

    def __str__(self):
        return "(eval" + self.term.__str__() + ")"


class PolyFactor:
    def __init__(self, term):
        self.term = term

    def __str__(self):
        return "(poly/factor" + self.term.__str__() + ")"


class CheckSat:
    def __init__(self, terms=None):
        self.terms = terms

    def __str__(self):
        t_str = ""
        if self.terms:
            t_str = ""
            for t in self.terms:
                t_str += " " + t.__str__()
            return "(check-sat" + t_str + ")"
        return "(check-sat)"


class CheckSatAssuming:
    def __init__(self, terms):
        self.terms = terms

    def __str__(self):
        s_term = self.terms[0].__str__()
        for t in self.terms[1:]:
            s_term += " " + t.__str__()
        return "(check-sat-assuming (" + s_term + "))"


class GetValue:
    def __init__(self, terms):
        self.terms = terms

    def __str__(self):
        t_str = ""
        for t in self.terms:
            t_str += t.__str__()
        return "(get-value (" + t_str + "))"


class Push:
    def __init__(self, terms=None):
        self.terms = terms

    def __str__(self):
        t_str = ""
        if self.terms:
            t_str = ""
            for t in self.terms:
                t_str += " " + t.__str__()
            return "(push" + t_str + ")"
        return "(push)"


class Pop:
    def __init__(self, terms=None):
        self.terms = terms

    def __str__(self):
        t_str = ""
        if self.terms:
            t_str = ""
            for t in self.terms:
                t_str += " " + t.__str__()
            return "(pop" + t_str + ")"
        return "(pop)"


class SMTLIBCommand:
    def __init__(self, cmd_str):
        self.cmd_str = cmd_str

    def __str__(self):
        return self.cmd_str

    def __eq__(self, other):
        if other.cmd_str == self.cmd_str:
            return True
        return False

    def __hash__(self):
        return self.cmd_str.__hash__()


def Var(name, type, is_indexed_id=False):
    return Term(name=name, type=type, is_var=True, is_indexed_id=is_indexed_id)


def Const(name, is_indexed_id=False, type="Unknown"):
    return Term(
        name=name, type=type, is_const=True, is_indexed_id=is_indexed_id
    )


def Expr(op, subterms, is_indexed_id=False):
    return Term(op=op, subterms=subterms)


def UnknownSymbol(name):
    return Term(name=name)


def Quantifier(quantifier, quantified_vars, subterms):
    return Term(
        quantifier=quantifier,
        quantified_vars=quantified_vars,
        subterms=subterms
    )


def LetBinding(var_binders, let_terms, subterms):
    return Term(
        var_binders=var_binders,
        let_terms=let_terms,
        subterms=subterms
    )


def LabeledTerm(label, subterms):
    return Term(label=label, subterms=subterms)


class Term:
    def __init__(
        self,
        name=None,
        type=None,
        is_const=None,
        is_var=None,
        label=None,
        indices=None,
        quantifier=None,
        quantified_vars={},
        var_binders=None,
        let_terms=None,
        op=None,
        subterms=None,
        is_indexed_id=False,
        parent=None,
    ):

        self._initialize(
            name=name,
            type=type,
            is_const=is_const,
            is_var=is_var,
            indices=indices,
            label=label,
            quantifier=quantifier,
            quantified_vars=quantified_vars,
            var_binders=var_binders,
            let_terms=let_terms,
            op=op,
            subterms=subterms,
            is_indexed_id=is_indexed_id,
            parent=parent,
        )
        self._add_parent_pointer()

    def _initialize(
        self,
        name=None,
        type=None,
        is_const=None,
        is_var=None,
        label=None,
        indices=None,
        quantifier=None,
        quantified_vars={},
        var_binders=None,
        let_terms=None,
        op=None,
        subterms=None,
        is_indexed_id=None,
        parent=None,
    ):
        self.name = name
        self.type = type
        self.is_const = is_const
        self.is_var = is_var
        self.label = label
        self.indices = indices
        self.quantifier = quantifier
        self.quantified_vars = quantified_vars
        self.var_binders = var_binders
        self.let_terms = let_terms
        self.op = op
        self.subterms = subterms
        self.is_indexed_id = is_indexed_id
        self.parent = parent

    def _add_parent_pointer(self):
        """
        Adds pointer from each element in subterm to expr.
        """
        if self.subterms:
            for term in self.subterms:
                if not isinstance(term, str):
                    term.parent = self

    def find_all(self, e, occs):
        """
        Find all expressions e in self and add them to the list occs.
        """
        if self == e:
            return occs.append(e)
        if self.subterms:
            for sub in self.subterms:
                if sub == e:
                    occs.append(sub)
                else:
                    sub.find_all(e, occs)

    def substitute(self, e, repl):
        """
        Substitute all expressions e in self by repl.
        """
        occs = []
        self.find_all(e, occs)
        for occ in occs:
            occ._initialize(
                name=copy.deepcopy(repl.name),
                type=copy.deepcopy(repl.type),
                is_const=copy.deepcopy(repl.is_const),
                is_var=copy.deepcopy(repl.is_var),
                label=copy.deepcopy(repl.label),
                indices=copy.deepcopy(repl.indices),
                quantifier=copy.deepcopy(repl.quantifier),
                quantified_vars=copy.deepcopy(repl.quantified_vars),
                var_binders=copy.deepcopy(repl.var_binders),
                let_terms=copy.deepcopy(repl.let_terms),
                op=copy.deepcopy(repl.op),
                subterms=copy.deepcopy(repl.subterms),
                is_indexed_id=copy.deepcopy(repl.is_indexed_id),
                parent=occ.parent,
            )

    def __eq__(self, other):
        if not isinstance(other, Term):
            return False
        if self.name != other.name:
            return False
        if self.type != other.type:
            return False
        if self.is_const != other.is_const:
            return False
        if self.is_var != other.is_var:
            return False
        if self.label != other.label:
            return False
        if self.indices != other.indices:
            return False
        if self.quantifier != other.quantifier:
            return False
        if self.quantified_vars != other.quantified_vars:
            return False
        if self.type != other.type:
            return False
        if self.is_var != other.is_var:
            return False
        if self.op != other.op:
            return False
        if self.subterms != other.subterms:
            return False
        if self.is_indexed_id != other.is_indexed_id:
            return False
        return True

    def __get_subterm_str__(self):
        subs_str = ""
        length = len(self.subterms)
        for i in range(length):
            sb = self.subterms[i]
            if i == length - 1:
                subs_str += sb.__str__()
            else:
                subs_str += sb.__str__() + " "
        return subs_str

    def __str__(self):
        if self.is_const or self.is_var or self.is_indexed_id:
            return self.name

        if self.quantifier:
            subs_str = self.__get_subterm_str__()
            n_vars = len(self.quantified_vars[0])
            s = (
                "("
                + self.quantified_vars[0][0]
                + " "
                + self.quantified_vars[1][0]
                + ")"
            )
            if len(self.quantified_vars[0]) > 1:
                for i in range(1, n_vars):
                    s += (
                        " ("
                        + self.quantified_vars[0][i]
                        + " "
                        + self.quantified_vars[1][i]
                        + ")"
                    )
            return "(" + self.quantifier + " (" + s + ") " + subs_str + ")"

        elif self.var_binders:
            s = "(let ("
            for i, var in enumerate(self.var_binders):
                s += "(" + var + " " + self.let_terms[i].__str__() + ")"
            s += ")"

            for sub in self.subterms:
                s += " " + sub.__str__()
            return s + ")"

        elif self.label:
            subs_str = self.__get_subterm_str__()
            return "(! "\
                   + subs_str + " "\
                   + self.label[0] + " " + self.label[1] + ")"
        else:
            subs_str = self.__get_subterm_str__()
            return "(" + self.op.__str__() + " " + subs_str + ")"

    def __repr__(self):
        if self.is_const:
            return self.name

        if self.is_var:
            return self.name + ":" + self.type
