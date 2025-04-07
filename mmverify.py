#!/usr/bin/env python3
"""mmverify.py -- Proof verifier for the Metamath language
Copyright (C) 2002 Raph Levien raph (at) acm (dot) org
Copyright (C) David A. Wheeler and mmverify.py contributors

This program is free software distributed under the MIT license;
see the file LICENSE for full license information.
SPDX-License-Identifier: MIT

To run the program, type
  $ python3 mmverify.py set.mm --logfile set.log
and set.log will have the verification results.  One can also use bash
redirections and type '$ python3 mmverify.py < set.mm 2> set.log' but this
would fail in case 'set.mm' contains (directly or not) a recursive inclusion
statement $[ set.mm $] .

To get help on the program usage, type
  $ python3 mmverify.py -h

(nm 27-Jun-2005) mmverify.py requires that a $f hypothesis must not occur
after a $e hypothesis in the same scope, even though this is allowed by
the Metamath spec.  This is not a serious limitation since it can be
met by rearranging the hypothesis order.
(rl 2-Oct-2006) removed extraneous line found by Jason Orendorff
(sf 27-Jan-2013) ported to Python 3, added support for compressed proofs
and file inclusion
(bj 3-Apr-2022) streamlined code; obtained significant speedup (4x on set.mm)
by verifying compressed proofs without converting them to normal proof format;
added type hints
(am 29-May-2023) added typeguards
"""

import sys
import itertools
import pathlib
import argparse
import typing
import io

# Imports added by Zarathustra
import re
from typing import Optional
import hyperon
# from hyperon import E,V,S

metta = hyperon.MeTTa()

# A log of all the MeTTa commands run
metta_log = []

# Run and Log a MeTTa Command
def mettarl(cmd: str):
    metta_log.append(cmd)
    return metta.run(cmd)

def mettify(expr) -> str:
    if expr == set():
        return "()"
    expr_str = str(expr)
    # Remove commas
    expr_str = expr_str.replace(",", "")
    # Replace square brackets with parentheses
    expr_str = expr_str.replace("[", "(")
    expr_str = expr_str.replace("]", ")")
    # Replace curly brackets with parentheses
    expr_str = expr_str.replace("{", "(")
    expr_str = expr_str.replace("}", ")")
    # Replace single quotes (often from Python strings in containers) with double quotes for MeTTa strings
    expr_str = expr_str.replace("'", '"')
    return expr_str

with open('mmverify-utils.metta', 'r') as f:
    MeTTa_Utils = f.read()

# Because we run the MeTTa_Utils, we add it to the log to make it self-contained.
MeTTa_Utils_Exprs = metta.parse_all(MeTTa_Utils)
for expr in MeTTa_Utils_Exprs:
    mettarl(str(expr))

# The MeTTa 'stack' to mirror the Metamath one.
mettarl('!(bind! &consts (new-space))') # Constanst
mettarl('!(bind! &stack (new-space))') # Stack in treat_proof
mettarl('!(bind! &labels (new-space))') # Labels
mettarl('!(bind! &subst (new-space))') # Substitution dict
mettarl('!(bind! &wm (new-space))') # Working Memory (safer than &self, easier to wipe, etc.)


Label = str
Var = str
Const = str
Stmttype = typing.Literal["$c", "$v", "$f", "$e", "$a", "$p", "$d", "$="]
StringOption = typing.Optional[str]
Symbol = typing.Union[Var, Const]
Stmt = list[Symbol]
Ehyp = Stmt
Fhyp = tuple[Const, Var]
Dv = tuple[Var, Var]
Assertion = tuple[set[Dv], list[Fhyp], list[Ehyp], Stmt]
FullStmt = tuple[Stmttype, typing.Union[Stmt, Assertion]]

def is_hypothesis(stmt: FullStmt) -> typing.TypeGuard[tuple[Stmttype, Stmt]]:
    """The second component of a FullStmt is a Stmt when its first
    component is '$e' or '$f'."""
    return stmt[0] in ('$e', '$f')

def is_assertion(stmt: FullStmt) -> typing.TypeGuard[tuple[Stmttype, Assertion]]:
    """The second component of a FullStmt is an Assertion if its first
    component is '$a' or '$p'."""
    return stmt[0] in ('$a', '$p')

# Note: a script at github.com/metamath/set.mm removes from the following code
# the lines beginning with (spaces followed by) 'vprint(' using the command
#   $ sed -E '/^ *vprint\(/d' mmverify.py > mmverify.faster.py
# In order that mmverify.faster.py be valid, one must therefore not break
# 'vprint' commands over multiple lines, nor have indented blocs containing
# only vprint lines (this would create ill-indented files).


class MMError(Exception):
    """Class of Metamath errors."""
    pass


class MMKeyError(MMError, KeyError):
    """Class of Metamath key errors."""
    pass


def vprint(vlevel: int, *arguments: typing.Any) -> None:
    """Print log message if verbosity level is higher than the argument."""
    if verbosity >= vlevel:
        print(*arguments, file=logfile)


class Toks:
    """Class of sets of tokens from which functions read as in an input
    stream.
    """

    def __init__(self, file: io.TextIOWrapper) -> None:
        """Construct a 'Toks' from the given file: initialize a line buffer
        containing the lines of the file, and initialize a set of imported
        files to a singleton containing that file, so as to avoid multiple
        imports.
        """
        self.files_buf = [file]
        self.tokbuf: list[str] = []
        self.imported_files = set({pathlib.Path(file.name).resolve()})

    def read(self) -> StringOption:
        """Read the next token in the token buffer, or if it is empty, split
        the next line into tokens and read from it."""
        while not self.tokbuf:
            if self.files_buf:
                line = self.files_buf[-1].readline()
            else:
                # There is no file to read from: this can only happen if end
                # of file is reached while within a ${ ... $} block.
                raise MMError("Unclosed ${ ... $} block at end of file.")
            if line:  # split the line into a list of tokens
                self.tokbuf = line.split()
                self.tokbuf.reverse()
            else:  # no line: end of current file
                self.files_buf.pop().close()
                if not self.files_buf:
                    return None  # End of database
        tok = self.tokbuf.pop()
        vprint(90, "Token:", tok)
        return tok

    def readf(self) -> StringOption:
        """Read the next token once included files have been expanded.  In the
        latter case, the path/name of the expanded file is added to the set of
        imported files so as to avoid multiple imports.
        """
        tok = self.read()
        while tok == '$[':
            filename = self.read()
            if not filename:
                raise MMError(
                    "Unclosed inclusion statement at end of file.")
            endbracket = self.read()
            if endbracket != '$]':
                raise MMError(
                    ("Inclusion statement for file {} not " +
                     "closed with a '$]'.").format(filename))
            file = pathlib.Path(filename).resolve()
            if file not in self.imported_files:
                # wrap the rest of the line after the inclusion command in a
                # file object
                self.files_buf.append(
                    io.StringIO(
                        " ".join(
                            reversed(
                                self.tokbuf))))
                self.tokbuf = []
                self.files_buf.append(open(file, mode='r', encoding='ascii'))
                self.imported_files.add(file)
                vprint(5, 'Importing file:', filename)
            tok = self.read()
        vprint(80, "Token once included files expanded:", tok)
        return tok

    def readc(self) -> StringOption:
        """Read the next token once included files have been expanded and
        comments have been skipped.
        """
        tok = self.readf()
        while tok == '$(':
            # Note that we use 'read' in this while-loop, and not 'readf',
            # since inclusion statements within a comment are still comments
            # so should be skipped.
            # The following line is not necessary but makes things clearer;
            # note the similarity with the first three lines of 'readf'.
            tok = self.read()
            while tok and tok != '$)':
                if '$(' in tok or '$)' in tok:
                    raise MMError(
                        ("Encountered token '{}' while reading a comment. " +
                         "Comment contents should not contain '$(' nor " +
                         "'$)' as a substring.  In particular, comments " +
                         "should not nest.").format(tok))
                tok = self.read()
            if not tok:
                raise MMError("Unclosed comment at end of file.")
            assert tok == '$)'
            # 'readf' since an inclusion may follow a comment immediately
            tok = self.readf()
        vprint(70, "Token once comments skipped:", tok)
        return tok


class Frame:
    """Class of frames, keeping track of the environment."""

    def __init__(self) -> None:
        """Construct an empty frame."""
        self.v: set[Var] = set()
        self.d: set[Dv] = set()
        self.f: list[Fhyp] = []
        self.f_labels: dict[Var, Label] = {}
        self.e: list[Ehyp] = []
        self.e_labels: dict[tuple[Symbol, ...], Label] = {}
        # Note: both self.e and self.e_labels are needed since the keys of
        # self.e_labels form a set, but the order and repetitions of self.e
        # are needed.


class FrameStack(list[Frame]):
    """Class of frame stacks, which extends lists (considered and used as
    stacks).
    """

    def push(self) -> None:
        """Push an empty frame to the stack."""
        self.append(Frame())

    def add_e(self, stmt: Stmt, label: Label) -> None:
        """Add an essential hypothesis (token tuple) to the frame stack
        top.
        """
        frame = self[-1]
        frame.e.append(stmt)
        frame.e_labels[tuple(stmt)] = label
        # conversion to tuple since dictionary keys must be hashable
        mettarl(f'!(add-atom &labels ( (Label {mettify(label)}) EHyp ( (FSDepth {len(self)}) (ENum {len(frame.e)}) (Statement {mettify(stmt)}) (Type "$e") )))')

    def add_d(self, varlist: list[Var]) -> None:
        """Add a disjoint variable condition (ordered pair of variables) to
        the frame stack top.
        """
        new_dvs = set((min(x, y), max(x, y))
                          for x, y in itertools.product(varlist, varlist)
                          if x != y)
        self[-1].d.update(new_dvs)
        if new_dvs: # Only log if there are actual pairs
            dv_pairs_metta = " ".join(f'("{x}" "{y}")' for x, y in list(new_dvs))
            mettarl(f'!(add-atom &labels (DVar ( (FSDepth {len(self)}) (DVars {dv_pairs_metta} ) (Type "$d") )))')

    def lookup_v(self, tok: Var) -> bool:
        """Return whether the given token is an active variable."""
        return any(tok in fr.v for fr in self)

    def lookup_d(self, x: Var, y: Var) -> bool:
        """Return whether the given ordered pair of tokens belongs to an
        active disjoint variable statement.
        """
        return any((min(x, y), max(x, y)) in fr.d for fr in self)

    def lookup_f(self, var: Var) -> typing.Optional[Label]:
        """Return the label of the active floating hypothesis which types the
        given variable.
        """
        for frame in self:
            try:
                return frame.f_labels[var]
            except KeyError:
                pass
        return None  # Variable is not actively typed

    def lookup_e(self, stmt: Stmt) -> Label:
        """Return the label of the (earliest) active essential hypothesis with
        the given statement.
        """
        stmt_t = tuple(stmt)
        for frame in self:
            try:
                return frame.e_labels[stmt_t]
            except KeyError:
                pass
        raise MMKeyError(stmt_t)

    def find_vars(self, stmt: Stmt) -> set[Var]:
        """Return the set of variables in the given statement."""
        return {x for x in stmt if self.lookup_v(x)}

    def make_assertion(self, stmt: Stmt) -> Assertion:
        """Return a quadruple (disjoint variable conditions, floating
        hypotheses, essential hypotheses, conclusion) describing the given
        assertion.
        """
        e_hyps = [eh for fr in self for eh in fr.e]
        mand_vars = {tok for hyp in itertools.chain(e_hyps, [stmt])
                     for tok in hyp if self.lookup_v(tok)}
        dvs = {(x, y) for fr in self for (x, y)
               in fr.d if x in mand_vars and y in mand_vars}
        f_hyps = []
        for fr in self:
            for typecode, var in fr.f:
                if var in mand_vars:
                    f_hyps.append((typecode, var))
                    mand_vars.remove(var)
        assertion = dvs, f_hyps, e_hyps, stmt
        vprint(18, 'Make assertion:', assertion)
        return assertion

def metta_apply_subst(stmt: list[str], subst: dict[str, list[str]]) -> list[str]:
    """
    Calls the MeTTa-side apply_subst function to do the rewriting in MeTTa,
    then parses the result back into Python tokens.
    """

    # 1. Convert 'stmt' to a MeTTa tuple of quoted tokens,
    #    e.g.  ( "wff" "(" "P" "->" "Q" ")" )
    stmt_metta = " ".join(f'"{t}"' for t in stmt)
    stmt_expr = f'( {stmt_metta} )'

    # 2. Convert 'subst' to a (Substitution (("var" ("token1" "token2" ...))...))
    # -- Updated to store singletons as "tok" instead of ( "tok" ).
    #    e.g.  (Substitution (("P" ( "(" "t" "+" "0" ")" "=" "t" )) ("Q" ( "t" "=" "t" ))))
    dict_items = []
    for k, expansions in subst.items():
        if len(expansions) == 1:
            dict_items.append(f'("{k}" "{expansions[0]}")')
        else:
            expansions_str = " ".join(f'"{tok}"' for tok in expansions)
            dict_items.append(f'("{k}" ( {expansions_str} ))')
    if dict_items:
        dict_str = " ".join(dict_items)
        subst_expr = f'(py-dict ({dict_str}))'
    else:
        subst_expr = '(py-dict ())'
    # if dict_items:
    #     dict_str = " ".join(dict_items)
    #     subst_expr = f'(Substitution ({dict_str}))'
    # else:
    #     subst_expr = '(Substitution ())'

    # 3. Build the entire MeTTa call to "apply_subst"
    #    We'll do an exclamation "!" to evaluate it and get the final output.
    metta_code = f'!(apply_subst {stmt_expr} {subst_expr})'

    # 4. Run the code in MeTTa
    result = mettarl(metta_code)

    # The 'result' is typically a list-of-lists. For example:
    #   [[("wff" "(" ("(" "t" "+" "0" ")" "=" "t") "->" ("t" "=" "t") ")")]]
    # We want to parse out the tokens. Usually the top-level is a 2D structure:
    #   [ [... the actual expression ...] ].
    # So let's see if we can convert it to a Python list of strings.

    if not result:
        # If no result or something weird, return empty
        return []

    # 'result' might look like:
    # [[("wff" "(" ("(" "t" "+" "0" ")" "=" "t") "->" ("t" "=" "t") ")")]]

    vprint(99, 'MeTTa Substitution result', result, 'code', metta_code)
    # The easiest is to do a small helper that descends the structure you get:
    py_list = _extract_tokens(result[0][0])  # might be a tuple ExpressionAtom
    return py_list

LIST_OF_QUOTED = re.compile(r'^\(\s*(?:"[^"]+"\s*)+\)$')

def _extract_tokens(expr):
    """
    Flatten a MeTTa ExpressionAtom by calling expr.iterate(),
    each child is turned into a string, then we do a small
    regex check to see if it is:
      - A parenthesized list of quotes, e.g. ("t" "0")
      - A single quoted token, e.g. "t"
      - Otherwise we keep the raw string.
    """
    # If 'expr' doesn't have iterate(), fallback to str(expr).
    try:
        children = expr.iterate()
    except AttributeError:
        return [str(expr)]

    tokens = []
    for child in children:
        s = str(child).strip()

        # 1. If s looks like ("foo" "bar"), let's parse them out with a regex
        #    so ("t") => ["t"], ("t" "0") => ["t","0"]
        if LIST_OF_QUOTED.match(s):
            # Extract everything inside ( ... ) then find all "..."
            inside = s[1:-1].strip()   # remove outer parentheses
            found = re.findall(r'"([^"]+)"', inside)
            if found:
                tokens.extend(found)
                continue

        # 2. If it's exactly "something", remove the outer quotes
        if len(s) >= 2 and s[0] == '"' and s[-1] == '"':
            s = s[1:-1]

        tokens.append(s)

    return tokens

def apply_subst(stmt: Stmt, subst: dict[Var, Stmt]) -> Stmt:
    """Return the token list resulting from the given substitution
    (dictionary) applied to the given statement (token list).
    """
    result = []
    for tok in stmt:
        if tok in subst:
            result += subst[tok]
        else:
            result.append(tok)
    vprint(20, 'Applying subst', subst, 'to stmt', stmt, ':', result)
    # record_apply_subst(subst, stmt, result)
    # store_subst_in_metta(stmt, subst, result)
    # metta_result = metta_apply_subst(stmt, subst)
    # assert result == metta_result, f"Metta-Py Mismatch! {result} != {metta_result}"
    return result


class MM:
    """Class of ("abstract syntax trees" describing) Metamath databases."""

    def __init__(self, begin_label: Label, stop_label: Label) -> None:
        """Construct an empty Metamath database."""
        self.constants: set[Const] = set()
        self.fs = FrameStack()
        self.labels: dict[Label, FullStmt] = {}
        self.begin_label = begin_label
        self.stop_label = stop_label
        self.verify_proofs = not self.begin_label

    def add_c(self, tok: Const) -> None:
        """Add a constant to the database."""
        if tok in self.constants:
            raise MMError(
                'Constant already declared: {}'.format(tok))
        if self.fs.lookup_v(tok):
            raise MMError(
                'Trying to declare as a constant an active variable: {}'.format(tok))
        self.constants.add(tok)
        mettarl(f'!(add-atom &consts ( Constant ( (Symbol "{tok}") (Type "$c") )))')

    def add_v(self, tok: Var) -> None:
        """Add a variable to the frame stack top (that is, the current frame)
        of the database.  Allow local variable declarations.
        """
        if self.fs.lookup_v(tok):
            raise MMError('var already declared and active: {}'.format(tok))
        if tok in self.constants:
            raise MMError(
                'var already declared as constant: {}'.format(tok))
        self.fs[-1].v.add(tok)

    def add_f(self, typecode: Const, var: Var, label: Label) -> None:
        """Add a floating hypothesis (ordered pair (variable, typecode)) to
        the frame stack top (that is, the current frame) of the database.
        """
        if not self.fs.lookup_v(var):
            raise MMError('var in $f not declared: {}'.format(var))
        if typecode not in self.constants:
            raise MMError('typecode in $f not declared: {}'.format(typecode))
        if any(var in fr.f_labels for fr in self.fs):
            raise MMError(
                ("var in $f already typed by an active " +
                 "$f-statement: {}").format(var))
        frame = self.fs[-1]
        frame.f.append((typecode, var))
        frame.f_labels[var] = label

    def readstmt_aux(
            self,
            stmttype: Stmttype,
            toks: Toks,
            end_token: str) -> Stmt:
        """Read tokens from the input (assumed to be at the beginning of a
        statement) and return the list of tokens until the end_token
        (typically "$=" or "$.").
        """
        stmt = []
        tok = toks.readc()
        while tok and tok != end_token:
            is_active_var = self.fs.lookup_v(tok)
            if stmttype in {'$d', '$e', '$a', '$p'} and not (
                    tok in self.constants or is_active_var):
                raise MMError(
                    "Token {} is not an active symbol".format(tok))
            if stmttype in {
                '$e',
                '$a',
                    '$p'} and is_active_var and not self.fs.lookup_f(tok):
                raise MMError(("Variable {} in {}-statement is not typed " +
                               "by an active $f-statement).").format(tok, stmttype))
            stmt.append(tok)
            tok = toks.readc()
        if not tok:
            raise MMError(
                "Unclosed {}-statement at end of file.".format(stmttype))
        assert tok == end_token
        vprint(20, 'Statement:', stmt)
        return stmt

    def read_non_p_stmt(self, stmttype: Stmttype, toks: Toks) -> Stmt:
        """Read tokens from the input (assumed to be at the beginning of a
        non-$p-statement) and return the list of tokens until the next
        end-statement token '$.'.
        """
        return self.readstmt_aux(stmttype, toks, end_token="$.")

    def read_p_stmt(self, toks: Toks) -> tuple[Stmt, Stmt]:
        """Read tokens from the input (assumed to be at the beginning of a
        p-statement) and return the couple of lists of tokens (stmt, proof)
        appearing in "$p stmt $= proof $.".
        """
        stmt = self.readstmt_aux("$p", toks, end_token="$=")
        proof = self.readstmt_aux("$=", toks, end_token="$.")
        return stmt, proof

    def read(self, toks: Toks) -> None:
        """Read the given token list to update the database and verify its
        proofs.
        """
        self.fs.push()
        label = None
        tok = toks.readc()
        while tok and tok != '$}':
            if tok == '$c':
                for tok in self.read_non_p_stmt(tok, toks):
                    self.add_c(tok)
            elif tok == '$v':
                for tok in self.read_non_p_stmt(tok, toks):
                    self.add_v(tok)
            elif tok == '$f':
                stmt = self.read_non_p_stmt(tok, toks)
                if not label:
                    raise MMError(
                        '$f must have label (statement: {})'.format(stmt))
                if len(stmt) != 2:
                    raise MMError(
                        '$f must have length two but is {}'.format(stmt))
                self.add_f(stmt[0], stmt[1], label)
                self.labels[label] = ('$f', [stmt[0], stmt[1]])
                mettarl(f'!(add-atom &labels ( (Label {label}) FHyp ( (FSDepth {len(self.fs)}) (Typecode "{mettify(stmt[0])}") (FVar {mettify(stmt[1])}) (Type "$f") )))')
                label = None
            elif tok == '$e':
                if not label:
                    raise MMError('$e must have label')
                stmt = self.read_non_p_stmt(tok, toks)
                self.fs.add_e(stmt, label)
                self.labels[label] = ('$e', stmt)
                label = None
            elif tok == '$a':
                if not label:
                    raise MMError('$a must have label')
                dvs, f_hyps, e_hyps, stmt = self.fs.make_assertion(self.read_non_p_stmt(tok, toks))
                self.labels[label] = ('$a', (dvs, f_hyps, e_hyps, stmt))
                mettarl(f'!(add-atom &labels ( (Label {label}) Assertion ( (FSDepth {len(self.fs)}) (DVars {mettify(dvs)}) (FHyps {mettify(f_hyps)}) (EHyps {mettify(e_hyps)}) (Statement {mettify(stmt)}) (Type "$a") )))')
                label = None
            elif tok == '$p':
                if not label:
                    raise MMError('$p must have label')
                stmt, proof = self.read_p_stmt(toks)
                dvs, f_hyps, e_hyps, conclusion = self.fs.make_assertion(stmt)
                if self.verify_proofs:
                    vprint(2, 'Verify:', label)
                    self.verify(f_hyps, e_hyps, conclusion, proof)
                self.labels[label] = ('$p', (dvs, f_hyps, e_hyps, conclusion))
                mettarl(f'!(add-atom &labels ( (Label {label}) Proof ( (FSDepth {len(self.fs)}) (DVars {mettify(dvs)}) (FHyps {mettify(f_hyps)}) (EHyps {mettify(e_hyps)}) (Statement {mettify(stmt)}) (Type "$p") (ProofSequence {mettify(proof)}))))')
                label = None
            elif tok == '$d':
                self.fs.add_d(self.read_non_p_stmt(tok, toks))
            elif tok == '${':
                self.read(toks)
            elif tok == '$)':
                raise MMError("Unexpected '$)' while not within a comment")
            elif tok[0] != '$':
                if tok in self.labels:
                    raise MMError("Label {} multiply defined.".format(tok))
                label = tok
                vprint(20, 'Label:', label)
                if label == self.stop_label:
                    # TODO: exit gracefully the nested calls to self.read()
                    sys.exit(0)
                if label == self.begin_label:
                    self.verify_proofs = True
            else:
                raise MMError("Unknown token: '{}'.".format(tok))
            tok = toks.readc()
        self.fs.pop()

    def treat_step(self,
                   step: FullStmt,
                   stack: list[Stmt],
                   label: Optional[Label] = None) -> None:
        """Carry out the given proof step (given the label to treat and the
        current proof stack).  This modifies the given stack in place.
        """
        vprint(10, 'Proof step:', step)
        if is_hypothesis(step):
            _steptype, stmt = step
            stack.append(stmt)
            # This version keeps the F and EHyp checking because I'll need that for the pure-MeTTa version
            mettarl(f'!(match &labels ((Label {label}) $type $d) (if (or (== $type FHyp) (== $type EHyp)) (add-atom &stack ( (Num {len(stack)}) (Label {label}) $type $d)) (empty)))')
            ## The fully MeTTa asserts work.  Python is faster.  Order may only work because it's in that order in MeTTa's expressions.
            assert stmt == [x[1].strip('"') for x in (g.split() for g in re.findall(r'\(([^()]+)\)', str(metta.run(f'!(match &stack ( (Num 1) $l $t $d ) $d)')[0][0]))) if x[0] in ('Typecode', 'FVar')]
            # assert stmt[0] == str(metta.run(f'!(match &stack ( (Num 1) $l $t $d ) (match-atom $d (Typecode $tc) $tc))')[0][0]).strip('"')
            # assert stmt[1] == str(metta.run(f'!(match &stack ( (Num 1) $l $t $d ) (match-atom $d (FVar $fv) $fv))')[0][0])
        elif is_assertion(step):
            _steptype, assertion = step
            dvs0, f_hyps0, e_hyps0, conclusion0 = assertion
            # metta_dvs0 = {tuple(part.strip() for part in str(t).strip('"()').split(',')) for t in metta.run(f'!(match &labels ((Label {label}) Assertion $Data) (match-atom $Data (DVars $dvs) (match-atom $dvs ($x $y) (format-args ({{}},{{}}) ($x $y)))))')[0]}
            # assert dvs0 == metta_dvs0
            npop = len(f_hyps0) + len(e_hyps0)
            sp = len(stack) - npop
            mout = mettarl(f'''!(match &labels ((Label {label}) Assertion $Data)
                (let*
                    (
                    (() (match-atom $Data (DVars $dvars) (add-atom &wm (DVars $dvars))))
                    (() (match-atom $Data (FHyps $fhyps) (add-atom &wm (FHypse $fhyps))))
                    (() (match-atom $Data (EHyps $ehyps) (add-atom &wm (EHypse $ehyps))))
                    (() (match-atom $Data (Statement $statement) (add-atom &wm (Statement $statement))))
                    )
                    ($dvars $fhyps $ehyps $statement)))''')[0]
            print(mout)
            def top_groups(s): s=s.strip()[1:-1];g=[];d=0;st=0;[(d:=d+1,st:=i if d==1 else st) if c=='(' else(d:=d-1,g.append(s[st:i+1]) if d==0 else None) if c==')' else None for i,c in enumerate(s)];return g
            groups = top_groups(str(mout[0])); 
            mdvs0 = set(re.findall(r'"([^"]+)"', groups[0])); 
            mf_hyps0 = [tuple(re.findall(r'"([^"]+)"', g)) for g in top_groups(groups[1])]; 
            me_hyps0 = [list(re.findall(r'"([^"]+)"', g)) for g in top_groups(groups[2])]            
            mconclusion0 = re.findall(r'"([^"]+)"', groups[3])
            print(mdvs0, mf_hyps0, me_hyps0, mconclusion0)
            print(assertion)
            assert dvs0 == mdvs0
            assert f_hyps0 == mf_hyps0
            assert e_hyps0 == me_hyps0
            assert conclusion0 == mconclusion0
            # print(f'stack: {stack}')
            # mout = mettarl(f'''!(match &labels ((Label {label}) Assertion $Data)
            #     (let*
            #       ( ($lenf (match-atom $Data (FHyps $fhyps) (size-atom $fhyps))) 
            #         ($lene (match-atom $Data (EHyps $ehyps) (size-atom $ehyps)))
            #         ($npop (+ $lenf $lene))
            #         ($slen (let $nums (collapse (let $nums (match &stack ( (Num $n) $l $t $d ) $n) $nums)) (max-atom $nums)))
            #         ($sp   (- $slen $npop))) 
            #         (if (< $sp 0)
            #         (let $error (format-args (Stack underflow: proof step requires too many ({{}}) hypotheses.\nData is lf: {{}} vs {len(f_hyps0)}, le: {{}} vs {len(e_hyps0)}, slen: {{}} vs {len(stack)}, sp: {{}} vs {sp} ) ($npop $lenf $lene $slen $sp) ) (Error ((Label {label}) Assertion $Data) $error))
            #         (let () (add-atom &wm (sp $sp)) ($lenf $lene $npop $slen $sp)))))''')
            # print(assertion)
            # print(f'label {label}, sp: {sp}, npop:{npop}, assertion: {assertion}, metta: {metta.run('!(match &wm (sp $sp) $sp)')}')
            # print(f'mout: {mout}')
            # # print(f'metta stack size: {metta.run(f'!(let $nums (collapse (let $nums (match &stack ( (Num $n) $l $t $d ) $n) $nums)) (max-atom $nums))')}')
            # metta_sp = int(float(str(metta.run('!(match &wm (sp $sp) $sp)')[0][0])))
            # assert sp == metta_sp
            if sp < 0:
                raise MMError(
                    ("Stack underflow: proof step {} requires too many " +
                     "({}) hypotheses.").format(
                        step,
                        npop))
            subst: dict[Var, Stmt] = {}
            for typecode, var in f_hyps0:
                entry = stack[sp]
                if entry[0] != typecode:
                    raise MMError(
                        ("Proof stack entry {} does not match floating " +
                         "hypothesis ({}, {}).").format(entry, typecode, var))
                subst[var] = entry[1:]
                sp += 1
            vprint(15, 'Substitution to apply:', subst)
            for h in e_hyps0:
                entry = stack[sp]
                subst_h = apply_subst(h, subst)
                if entry != subst_h:
                    raise MMError(("Proof stack entry {} does not match " +
                                   "essential hypothesis {}.")
                                  .format(entry, subst_h))
                sp += 1
            for x, y in dvs0:
                vprint(16, 'dist', x, y, subst[x], subst[y])
                x_vars = self.fs.find_vars(subst[x])
                y_vars = self.fs.find_vars(subst[y])
                vprint(16, 'V(x) =', x_vars)
                vprint(16, 'V(y) =', y_vars)
                for x0, y0 in itertools.product(x_vars, y_vars):
                    if x0 == y0 or not self.fs.lookup_d(x0, y0):
                        raise MMError("Disjoint variable violation: " +
                                      "{} , {}".format(x0, y0))
            del stack[len(stack) - npop:]
            stack.append(apply_subst(conclusion0, subst))
        vprint(12, 'Proof stack:', stack)

    def treat_normal_proof(self, proof: list[str]) -> list[Stmt]:
        """Return the proof stack once the given normal proof has been
        processed.
        """
        stack: list[Stmt] = []
        active_hypotheses = {label for frame in self.fs for labels in (frame.f_labels, frame.e_labels) for label in labels.values()}
        mettarl(f'''!(add-atom &wm (ActiveHyps 
                        (collapse (let $current_depth 1 ; Example depth
                        (match &labels ((Label $L) $Type $Data)
                            (if (or (== $Type FHyp) (== $Type EHyp))
                                (match-atom $Data (FSDepth $D)
                                    (if (<= $D $current_depth) $L (empty)))
                                (empty) ))))))''')
        for label in proof:
            stmt_info = self.labels.get(label)
            if stmt_info:
                label_type = stmt_info[0]
                if label_type in {'$e', '$f'}:
                    if label in active_hypotheses:
                        self.treat_step(stmt_info, stack, label)
                    else:
                        raise MMError(f"The label {label} is the label of a nonactive hypothesis.")
                else:
                    self.treat_step(stmt_info, stack, label)
            else:
                raise MMError(f"No statement information found for label {label}")
        return stack
    
    def treat_compressed_proof(
            self,
            f_hyps: list[Fhyp],
            e_hyps: list[Ehyp],
            proof: list[str]) -> list[Stmt]:
        """Return the proof stack once the given compressed proof for an
        assertion with the given $f and $e-hypotheses has been processed.
        """
        # Preprocessing and building the lists of proof_ints and labels
        flabels = [self.fs.lookup_f(v) for _, v in f_hyps]
        elabels = [self.fs.lookup_e(s) for s in e_hyps]
        plabels = flabels + elabels  # labels of implicit hypotheses
        idx_bloc = proof.index(')')  # index of end of label bloc
        plabels += proof[1:idx_bloc]  # labels which will be referenced later
        compressed_proof = ''.join(proof[idx_bloc + 1:])
        vprint(5, 'Referenced labels:', plabels)
        label_end = len(plabels)
        vprint(5, 'Number of referenced labels:', label_end)
        vprint(5, 'Compressed proof steps:', compressed_proof)
        vprint(5, 'Number of steps:', len(compressed_proof))
        proof_ints = []  # integers referencing the labels in 'labels'
        cur_int = 0  # counter for radix conversion
        for ch in compressed_proof:
            if ch == 'Z':
                proof_ints.append(-1)
            elif 'A' <= ch <= 'T':
                proof_ints.append(20 * cur_int + ord(ch) - 65)  # ord('A') = 65
                cur_int = 0
            else:  # 'U' <= ch <= 'Y'
                cur_int = 5 * cur_int + ord(ch) - 84  # ord('U') = 85
        vprint(5, 'Integer-coded steps:', proof_ints)
        # Processing of the proof
        stack: list[Stmt] = []  # proof stack
        # statements saved for later reuse (marked with a 'Z')
        saved_stmts = []
        # can be recovered as len(saved_stmts) but less efficient
        n_saved_stmts = 0
        for proof_int in proof_ints:
            if proof_int == -1:  # save the current step for later reuse
                stmt = stack[-1]
                vprint(15, 'Saving step', stmt)
                saved_stmts.append(stmt)
                n_saved_stmts += 1
            elif proof_int < label_end:
                # proof_int denotes an implicit hypothesis or a label in the
                # label bloc
                self.treat_step(self.labels[plabels[proof_int] or ''], stack)
            elif proof_int >= label_end + n_saved_stmts:
                MMError(
                    ("Not enough saved proof steps ({} saved but calling " +
                    "the {}th).").format(
                        n_saved_stmts,
                        proof_int))
            else:  # label_end <= proof_int < label_end + n_saved_stmts
                # proof_int denotes an earlier proof step marked with a 'Z'
                # A proof step that has already been proved can be treated as
                # a dv-free and hypothesis-free axiom.
                stmt = saved_stmts[proof_int - label_end]
                vprint(15, 'Reusing step', stmt)
                self.treat_step(
                    ('$a',
                     (set(), [], [], stmt)),
                    stack)
        return stack

    def verify(
            self,
            f_hyps: list[Fhyp],
            e_hyps: list[Ehyp],
            conclusion: Stmt,
            proof: list[str]) -> None:
        """Verify that the given proof (in normal or compressed format) is a
        correct proof of the given assertion.
        """
        # It would not be useful to also pass the list of dv conditions of the
        # assertion as an argument since other dv conditions corresponding to
        # dummy variables should be 'lookup_d'ed anyway.
        if proof[0] == '(':  # compressed format
            stack = self.treat_compressed_proof(f_hyps, e_hyps, proof)
        else:  # normal format
            stack = self.treat_normal_proof(proof)
        vprint(10, 'Stack at end of proof:', stack)
        if not stack:
            raise MMError(
                "Empty stack at end of proof.")
        if len(stack) > 1:
            raise MMError(
                "Stack has more than one entry at end of proof (top " +
                "entry: {} ; proved assertion: {}).".format(
                    stack[0],
                    conclusion))
        if stack[0] != conclusion:
            raise MMError(("Stack entry {} does not match proved " +
                          " assertion {}.").format(stack[0], conclusion))
        vprint(3, 'Correct proof!')

    def dump(self) -> None:
        """Print the labels of the database."""
        print(self.labels)


if __name__ == '__main__':
    """Parse the arguments and verify the given Metamath database."""
    parser = argparse.ArgumentParser(description="""Verify a Metamath database.
      The grammar of the whole file is verified.  Proofs are verified between
      the statements with labels BEGIN_LABEL (included) and STOP_LABEL (not
      included).

      One can also use bash redirections:
         '$ python3 mmverify.py < file.mm 2> file.log'
      in place of
         '$ python3 mmverify.py file.mm --logfile file.log'
      but this fails in case 'file.mm' contains (directly or not) a recursive
      inclusion statement '$[ file.mm $]'.""")
    parser.add_argument(
        'database',
        nargs='?',
        type=argparse.FileType(
            mode='r',
            encoding='ascii'),
        default=sys.stdin,
        help="""database (Metamath file) to verify, expressed using relative
          path (defaults to <stdin>)""")
    parser.add_argument(
        '-l',
        '--logfile',
        dest='logfile',
        type=argparse.FileType(
            mode='w',
            encoding='ascii'),
        default=sys.stderr,
        help="""file to output logs, expressed using relative path (defaults to
          <stderr>)""")
    parser.add_argument(
        '-v',
        '--verbosity',
        dest='verbosity',
        default=0,
        type=int,
        help='verbosity level (default=0 is mute; higher is more verbose)')
    parser.add_argument(
        '-b',
        '--begin-label',
        dest='begin_label',
        type=str,
        help="""label where to begin verifying proofs (included, if it is a
          provable statement)""")
    parser.add_argument(
        '-s',
        '--stop-label',
        dest='stop_label',
        type=str,
        help='label where to stop verifying proofs (not included)')
    args = parser.parse_args()
    verbosity = args.verbosity
    db_file = args.database
    logfile = args.logfile
    vprint(1, 'mmverify.py -- Proof verifier for the Metamath language')
    mm = MM(args.begin_label, args.stop_label)
    vprint(1, 'Reading source file "{}"...'.format(db_file.name))
    mm.read(Toks(db_file))
    vprint(1, 'No errors were found.')
    # mm.dump()

    # Write the MeTTa log :)
    with open('mettamath.metta', 'w') as out:
        for line in metta_log:
            out.write(line)
            if not line.endswith('\n'):
                out.write('\n')

