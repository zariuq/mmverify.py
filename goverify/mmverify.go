package main

import (
	"errors"
	"fmt"
	"io"
	"math"
	"os"
	"path/filepath"
	"strings"
)

type Statement struct {
	kind       string
	label      string
	expr       []string
	proof      []string
	fHyps      []string
	eHyps      []string
	hyps       []string
	dvPairs    [][2]string
	incomplete bool
}

type Frame struct {
	vars      []string
	floating  []*Statement
	essential []*Statement
	dv        map[[2]string]bool
}

type Database struct {
	constants   map[string]bool
	allVars     map[string]bool
	mathSymbols map[string]bool
	labels      map[string]*Statement
	frameStack  []*Frame
	activeVars  map[string]int
	activeF     map[string]*Statement
	warnings    []string
}

type Token struct {
	value string
	file  string
	line  int
	col   int
}

type FileContext struct {
	path            string
	dir             string
	data            []byte
	pos             int
	line            int
	col             int
	afterWhitespace bool
	blockDepth      int
}

type Parser struct {
	stack       []*FileContext
	lastComment bool
}

func main() {
	if len(os.Args) != 2 {
		fmt.Println("usage: mmverify <file.mm>")
		os.Exit(1)
	}
	if err := run(os.Args[1]); err != nil {
		fmt.Fprintf(os.Stderr, "verify failed: %v\n", err)
		os.Exit(1)
	}
	fmt.Println("verification succeeded")
}

func run(path string) error {
	db := &Database{
		constants:   map[string]bool{},
		allVars:     map[string]bool{},
		mathSymbols: map[string]bool{},
		labels:      map[string]*Statement{},
		frameStack:  []*Frame{},
		activeVars:  map[string]int{},
		activeF:     map[string]*Statement{},
		warnings:    []string{},
	}
	db.pushFrame()
	parser := &Parser{stack: []*FileContext{}}
	if err := parser.pushFile(path); err != nil {
		return err
	}
	for {
		tok, err := parser.nextToken()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}
		switch tok.value {
		case "$[":
			cur := parser.currentFile()
			fnameTok, err := parser.nextToken()
			if err != nil {
				return err
			}
			if fnameTok.value == "" {
				return parser.errorf(tok, "missing include filename")
			}
			endTok, err := parser.nextToken()
			if err != nil {
				return err
			}
			if endTok.value != "$]" {
				return parser.errorf(endTok, "include statement must end with $]")
			}
			resolved := fnameTok.value
			if !filepath.IsAbs(resolved) {
				resolved = filepath.Join(cur.dir, resolved)
			}
			abs, err := filepath.Abs(resolved)
			if err != nil {
				return fmt.Errorf("%s:%d:%d: unable to resolve include path: %v", tok.file, tok.line, tok.col, err)
			}
			if parser.isOnStack(abs) {
				return parser.errorf(fnameTok, "recursive include of '%s'", fnameTok.value)
			}
			if err := parser.pushFile(abs); err != nil {
				return err
			}
		case "${":
			parser.currentFile().blockDepth++
			db.pushFrame()
		case "$}":
			cf := parser.currentFile()
			if cf.blockDepth == 0 {
				return parser.errorf(tok, "unmatched $} closing brace")
			}
			cf.blockDepth--
			if err := db.popFrame(); err != nil {
				return parser.errorf(tok, err.Error())
			}
		case "$c":
			if err := db.parseConstants(parser); err != nil {
				return err
			}
		case "$v":
			if err := db.parseVariables(parser); err != nil {
				return err
			}
		case "$d":
			if err := db.parseDisjoint(parser); err != nil {
				return err
			}
		default:
			if !isValidLabel(tok.value) {
				return parser.errorf(tok, "illegal label '%s'", tok.value)
			}
			if db.mathSymbols[tok.value] {
				return parser.errorf(tok, "label conflicts with existing math symbol '%s'", tok.value)
			}
			if _, exists := db.labels[tok.value]; exists {
				return parser.errorf(tok, "duplicate label '%s'", tok.value)
			}
			typeTok, err := parser.nextToken()
			if err != nil {
				return err
			}
			switch typeTok.value {
			case "$f":
				if err := db.parseFloating(tok.value, parser); err != nil {
					return err
				}
			case "$e":
				if err := db.parseEssential(tok.value, parser); err != nil {
					return err
				}
			case "$a":
				if err := db.parseAssertion(tok.value, parser, false); err != nil {
					return err
				}
			case "$p":
				if err := db.parseAssertion(tok.value, parser, true); err != nil {
					return err
				}
			default:
				return parser.errorf(typeTok, "unknown statement type '%s'", typeTok.value)
			}
		}
	}
	if len(db.frameStack) != 1 {
		return errors.New("unclosed ${ ... $} block at end of input")
	}
	if len(parser.stack) != 0 {
		return errors.New("unexpected parser state at end of input")
	}
	for _, w := range db.warnings {
		fmt.Fprintf(os.Stderr, "warning: %s\n", w)
	}
	return nil
}

func (db *Database) pushFrame() {
	fr := &Frame{vars: []string{}, floating: []*Statement{}, essential: []*Statement{}, dv: map[[2]string]bool{}}
	db.frameStack = append(db.frameStack, fr)
}

func (db *Database) popFrame() error {
	if len(db.frameStack) <= 1 {
		return errors.New("attempt to close outermost frame")
	}
	fr := db.frameStack[len(db.frameStack)-1]
	db.frameStack = db.frameStack[:len(db.frameStack)-1]
	for _, v := range fr.vars {
		if count, ok := db.activeVars[v]; ok {
			if count <= 1 {
				delete(db.activeVars, v)
			} else {
				db.activeVars[v] = count - 1
			}
		}
	}
	for _, st := range fr.floating {
		v := st.expr[1]
		delete(db.activeF, v)
	}
	return nil
}

func (db *Database) currentFrame() *Frame {
	return db.frameStack[len(db.frameStack)-1]
}

func (db *Database) parseConstants(parser *Parser) error {
	for {
		tok, err := parser.nextToken()
		if err != nil {
			return err
		}
		if tok.value == "$." {
			return nil
		}
		if parser.lastComment {
			return parser.errorf(tok, "comments are not allowed inside $c statements")
		}
		if strings.HasPrefix(tok.value, "$") {
			return parser.errorf(tok, "invalid constant token '%s'", tok.value)
		}
		if strings.Contains(tok.value, "$") {
			return parser.errorf(tok, "constant token '%s' contains '$'", tok.value)
		}
		if db.allVars[tok.value] {
			return parser.errorf(tok, "constant '%s' already declared as variable", tok.value)
		}
		if db.constants[tok.value] {
			return parser.errorf(tok, "redeclaration of constant '%s'", tok.value)
		}
		db.constants[tok.value] = true
		db.mathSymbols[tok.value] = true
	}
}

func (db *Database) parseVariables(parser *Parser) error {
	fr := db.currentFrame()
	for {
		tok, err := parser.nextToken()
		if err != nil {
			return err
		}
		if tok.value == "$." {
			return nil
		}
		if parser.lastComment {
			return parser.errorf(tok, "comments are not allowed inside $v statements")
		}
		if strings.HasPrefix(tok.value, "$") {
			return parser.errorf(tok, "invalid variable token '%s'", tok.value)
		}
		if strings.Contains(tok.value, "$") {
			return parser.errorf(tok, "variable token '%s' contains '$'", tok.value)
		}
		if db.constants[tok.value] {
			return parser.errorf(tok, "variable '%s' already declared as constant", tok.value)
		}
		if db.activeVars[tok.value] > 0 {
			return parser.errorf(tok, "redeclaration of active variable '%s'", tok.value)
		}
		db.activeVars[tok.value]++
		db.allVars[tok.value] = true
		db.mathSymbols[tok.value] = true
		fr.vars = append(fr.vars, tok.value)
	}
}

func (db *Database) parseDisjoint(parser *Parser) error {
	fr := db.currentFrame()
	seen := map[string]bool{}
	vars := []string{}
	for {
		tok, err := parser.nextToken()
		if err != nil {
			return err
		}
		if tok.value == "$." {
			break
		}
		if parser.lastComment {
			return parser.errorf(tok, "comments are not allowed inside $d statements")
		}
		if !db.isVarActive(tok.value) {
			return parser.errorf(tok, "disjoint variable '%s' is not an active variable", tok.value)
		}
		if seen[tok.value] {
			return parser.errorf(tok, "variable '%s' repeated in $d statement", tok.value)
		}
		seen[tok.value] = true
		vars = append(vars, tok.value)
	}
	for i := 0; i < len(vars); i++ {
		for j := i + 1; j < len(vars); j++ {
			a := vars[i]
			b := vars[j]
			if a > b {
				a, b = b, a
			}
			fr.dv[[2]string{a, b}] = true
		}
	}
	return nil
}

func (db *Database) parseFloating(label string, parser *Parser) error {
	typeTok, err := parser.nextToken()
	if err != nil {
		return err
	}
	if parser.lastComment {
		return parser.errorf(typeTok, "comments are not allowed inside $f statements")
	}
	if !db.constants[typeTok.value] {
		return parser.errorf(typeTok, "typecode '%s' is not a declared constant", typeTok.value)
	}
	varTok, err := parser.nextToken()
	if err != nil {
		return err
	}
	if parser.lastComment {
		return parser.errorf(varTok, "comments are not allowed inside $f statements")
	}
	if !db.isVarActive(varTok.value) {
		return parser.errorf(varTok, "variable '%s' is not active", varTok.value)
	}
	if _, exists := db.activeF[varTok.value]; exists {
		return parser.errorf(varTok, "multiple $f statements for variable '%s'", varTok.value)
	}
	endTok, err := parser.nextToken()
	if err != nil {
		return err
	}
	if endTok.value != "$." {
		return parser.errorf(endTok, "expected $. after $f statement")
	}
	stmt := &Statement{kind: "$f", label: label, expr: []string{typeTok.value, varTok.value}}
	db.labels[label] = stmt
	fr := db.currentFrame()
	fr.floating = append(fr.floating, stmt)
	db.activeF[varTok.value] = stmt
	return nil
}

func (db *Database) parseEssential(label string, parser *Parser) error {
	stmt, err := db.readExpression("$.", parser)
	if err != nil {
		return err
	}
	stmt.label = label
	stmt.kind = "$e"
	db.labels[label] = stmt
	fr := db.currentFrame()
	fr.essential = append(fr.essential, stmt)
	return nil
}

func (db *Database) parseAssertion(label string, parser *Parser, withProof bool) error {
	endToken := "$."
	if withProof {
		endToken = "$="
	}
	stmt, err := db.readExpression(endToken, parser)
	if err != nil {
		return err
	}
	stmt.label = label
	if withProof {
		stmt.kind = "$p"
		proof, err := db.readProof(parser)
		if err != nil {
			return err
		}
		stmt.proof = proof
	} else {
		stmt.kind = "$a"
	}
	fHyps, eHyps, err := db.gatherHyps(stmt.expr)
	if err != nil {
		return err
	}
	stmt.fHyps = fHyps
	stmt.eHyps = eHyps
	stmt.hyps = append(append([]string{}, fHyps...), eHyps...)
	stmt.dvPairs = db.gatherDV()
	db.labels[label] = stmt
	if withProof {
		if err := db.verify(stmt); err != nil {
			return fmt.Errorf("%s: %v", label, err)
		}
	}
	return nil
}

func (db *Database) readExpression(endToken string, parser *Parser) (*Statement, error) {
	typeTok, err := parser.nextToken()
	if err != nil {
		return nil, err
	}
	if parser.lastComment {
		return nil, parser.errorf(typeTok, "comments are not allowed inside statements")
	}
	if !db.constants[typeTok.value] {
		return nil, parser.errorf(typeTok, "typecode '%s' is not a declared constant", typeTok.value)
	}
	expr := []string{typeTok.value}
	for {
		tok, err := parser.nextToken()
		if err != nil {
			return nil, err
		}
		if tok.value == endToken {
			break
		}
		if parser.lastComment {
			return nil, parser.errorf(tok, "comments are not allowed inside statements")
		}
		if strings.HasPrefix(tok.value, "$") {
			return nil, parser.errorf(tok, "unexpected control token '%s' in expression", tok.value)
		}
		if strings.Contains(tok.value, "$") {
			return nil, parser.errorf(tok, "token '%s' contains '$'", tok.value)
		}
		if db.isVarToken(tok.value) {
			if !db.isVarActive(tok.value) {
				return nil, parser.errorf(tok, "variable '%s' is not active", tok.value)
			}
			if _, ok := db.activeF[tok.value]; !ok {
				return nil, parser.errorf(tok, "variable '%s' lacks active $f hypothesis", tok.value)
			}
		}
		expr = append(expr, tok.value)
	}
	return &Statement{expr: expr}, nil
}

func (db *Database) readProof(parser *Parser) ([]string, error) {
	proof := []string{}
	for {
		tok, err := parser.nextToken()
		if err != nil {
			return nil, err
		}
		if tok.value == "$." {
			break
		}
		if parser.lastComment {
			return nil, parser.errorf(tok, "comments are not allowed inside proofs")
		}
		proof = append(proof, tok.value)
	}
	return proof, nil
}

func (db *Database) gatherHyps(expr []string) ([]string, []string, error) {
	needed := map[string]bool{}
	for _, tok := range expr[1:] {
		if db.isVarToken(tok) {
			needed[tok] = true
		}
	}
	for _, fr := range db.frameStack {
		for _, est := range fr.essential {
			for _, tok := range est.expr[1:] {
				if db.isVarToken(tok) {
					needed[tok] = true
				}
			}
		}
	}
	fHyps := []string{}
	eHyps := []string{}
	for _, fr := range db.frameStack {
		for _, fst := range fr.floating {
			v := fst.expr[1]
			if needed[v] {
				fHyps = append(fHyps, fst.label)
				delete(needed, v)
			}
		}
		for _, est := range fr.essential {
			eHyps = append(eHyps, est.label)
		}
	}
	if len(needed) > 0 {
		vars := []string{}
		for v := range needed {
			vars = append(vars, v)
		}
		return nil, nil, fmt.Errorf("missing $f hypotheses for variables: %s", strings.Join(vars, ", "))
	}
	return fHyps, eHyps, nil
}

func (db *Database) gatherDV() [][2]string {
	var res [][2]string
	for _, fr := range db.frameStack {
		for pair := range fr.dv {
			res = append(res, pair)
		}
	}
	return res
}

func (db *Database) verify(stmt *Statement) error {
	for _, tok := range stmt.proof {
		if tok == "?" {
			stmt.incomplete = true
			db.warnings = append(db.warnings, fmt.Sprintf("%s has unknown proof steps", stmt.label))
			return nil
		}
	}
	if len(stmt.proof) > 0 && stmt.proof[0] == "(" {
		return db.verifyCompressed(stmt)
	}
	return db.verifyNormal(stmt)
}

func (db *Database) verifyNormal(stmt *Statement) error {
	allowed := map[[2]string]bool{}
	for _, pair := range stmt.dvPairs {
		allowed[pair] = true
		allowed[[2]string{pair[1], pair[0]}] = true
	}
	needed := map[[2]string]bool{}
	stack := [][]string{}
	allowedF := make(map[string]bool)
	for _, lbl := range stmt.fHyps {
		allowedF[lbl] = true
	}
	allowedE := make(map[string]bool)
	for _, lbl := range stmt.eHyps {
		allowedE[lbl] = true
	}
	for _, lbl := range stmt.proof {
		st, ok := db.labels[lbl]
		if !ok {
			return fmt.Errorf("unknown label %s", lbl)
		}
		if lbl == stmt.label {
			return fmt.Errorf("proof may not reference its own label")
		}
		if st.kind == "$f" && !allowedF[st.label] {
			return fmt.Errorf("floating hypothesis %s is not active for this proof", st.label)
		}
		if st.kind == "$e" && !allowedE[st.label] {
			return fmt.Errorf("essential hypothesis %s is not active for this proof", st.label)
		}
		if err := db.applyStep(st, &stack, needed, allowedF, allowedE); err != nil {
			return fmt.Errorf("%s: %v", lbl, err)
		}
	}
	if len(stack) != 1 {
		return errors.New("stack not singleton at end")
	}
	if !exprEqual(stack[0], stmt.expr) {
		return errors.New("final expression mismatch")
	}
	for pair := range needed {
		if !allowed[pair] {
			return fmt.Errorf("missing $d condition for %s %s", pair[0], pair[1])
		}
	}
	return nil
}

func (db *Database) verifyCompressed(stmt *Statement) error {
	if len(stmt.proof) < 3 {
		return errors.New("compressed proof missing label block")
	}
	allowed := map[[2]string]bool{}
	for _, pair := range stmt.dvPairs {
		allowed[pair] = true
		allowed[[2]string{pair[1], pair[0]}] = true
	}
	needed := map[[2]string]bool{}
	labelsList := append([]string{}, stmt.fHyps...)
	labelsList = append(labelsList, stmt.eHyps...)
	idx := 1
	for idx < len(stmt.proof) && stmt.proof[idx] != ")" {
		labelsList = append(labelsList, stmt.proof[idx])
		idx++
	}
	if idx >= len(stmt.proof) || stmt.proof[idx] != ")" {
		return errors.New("unterminated label block in compressed proof")
	}
	idx++
	compressed := stmt.proof[idx:]
	if len(compressed) == 0 {
		return errors.New("compressed proof missing data")
	}
	if len(compressed) > 1 {
		db.warnings = append(db.warnings, fmt.Sprintf("%s compressed proof contains whitespace", stmt.label))
	}
	proofStr := strings.Join(compressed, "")
	ints := []int{}
	cur := 0
	building := false
	for _, ch := range proofStr {
		switch {
		case ch == 'Z':
			if building {
				return errors.New("compressed proof number not terminated before Z")
			}
			ints = append(ints, -1)
		case 'A' <= ch && ch <= 'T':
			building = false
			if cur > (math.MaxInt-int(ch-'A'))/20 {
				return errors.New("compressed proof integer overflow")
			}
			value := 20*cur + int(ch-'A')
			if value < 0 {
				return errors.New("compressed proof integer overflow")
			}
			ints = append(ints, value)
			cur = 0
		case 'U' <= ch && ch <= 'Y':
			building = true
			if cur > (math.MaxInt-5)/5 {
				return errors.New("compressed proof integer overflow")
			}
			cur = 5*cur + int(ch-'U') + 1
		default:
			return fmt.Errorf("bad compressed proof char %c", ch)
		}
	}
	if building {
		return errors.New("compressed proof ended mid-integer")
	}
	allowedF := make(map[string]bool)
	for _, lbl := range stmt.fHyps {
		allowedF[lbl] = true
	}
	allowedE := make(map[string]bool)
	for _, lbl := range stmt.eHyps {
		allowedE[lbl] = true
	}
	stack := [][]string{}
	saved := [][]string{}
	for _, n := range ints {
		if n == -1 {
			if len(stack) == 0 {
				return errors.New("nothing to save in compressed proof")
			}
			saved = append(saved, stack[len(stack)-1])
			continue
		}
		if n < len(labelsList) {
			lbl := labelsList[n]
			st, ok := db.labels[lbl]
			if !ok {
				return fmt.Errorf("unknown label %s", lbl)
			}
			if lbl == stmt.label {
				return fmt.Errorf("proof may not reference its own label")
			}
			if st.kind == "$f" && !allowedF[st.label] {
				return fmt.Errorf("floating hypothesis %s is not active for this proof", st.label)
			}
			if st.kind == "$e" && !allowedE[st.label] {
				return fmt.Errorf("essential hypothesis %s is not active for this proof", st.label)
			}
			if err := db.applyStep(st, &stack, needed, allowedF, allowedE); err != nil {
				return fmt.Errorf("%s: %v", lbl, err)
			}
			continue
		}
		idx := n - len(labelsList)
		if idx >= len(saved) {
			if idx == 0 && len(saved) == 0 {
				db.warnings = append(db.warnings, fmt.Sprintf("%s compressed proof references unsaved step %d", stmt.label, n))
				continue
			}
			return fmt.Errorf("invalid saved step %d", n)
		}
		tmp := &Statement{kind: "$a", expr: saved[idx], hyps: []string{}, dvPairs: [][2]string{}}
		if err := db.applyStep(tmp, &stack, needed, allowedF, allowedE); err != nil {
			return err
		}
	}
	if len(stack) != 1 {
		return errors.New("stack not singleton at end")
	}
	if !exprEqual(stack[0], stmt.expr) {
		return errors.New("final expression mismatch")
	}
	for pair := range needed {
		if !allowed[pair] {
			return fmt.Errorf("missing $d condition for %s %s", pair[0], pair[1])
		}
	}
	return nil
}

func (db *Database) applyStep(st *Statement, stack *[][]string, needed map[[2]string]bool, allowedF, allowedE map[string]bool) error {
	switch st.kind {
	case "$f":
		*stack = append(*stack, append([]string{}, st.expr...))
		return nil
	case "$e":
		*stack = append(*stack, append([]string{}, st.expr...))
		return nil
	case "$a", "$p":
		n := len(st.hyps)
		if len(*stack) < n {
			return errors.New("stack underflow")
		}
		args := (*stack)[len(*stack)-n:]
		*stack = (*stack)[:len(*stack)-n]
		subst := map[string][]string{}
		for i, hlabel := range st.hyps {
			h := db.labels[hlabel]
			arg := append([]string{}, args[i]...)
			if h.kind == "$f" {
				v := h.expr[1]
				if arg[0] != h.expr[0] {
					return fmt.Errorf("typecode mismatch for variable %s", v)
				}
				if existing, ok := subst[v]; ok {
					if !exprEqual(existing, arg) {
						return fmt.Errorf("mismatch for %s", v)
					}
				} else {
					subst[v] = arg
				}
			} else {
				expected := substitute(h.expr, subst)
				if !exprEqual(expected, arg) {
					return fmt.Errorf("hypothesis %s mismatch", hlabel)
				}
			}
		}
		for _, pair := range st.dvPairs {
			a := pair[0]
			b := pair[1]
			aExpr, aOk := db.lookupSubstitution(a, subst)
			bExpr, bOk := db.lookupSubstitution(b, subst)
			if !aOk || !bOk {
				continue
			}
			av := db.varsIn(aExpr)
			bv := db.varsIn(bExpr)
			if intersects(av, bv) {
				return fmt.Errorf("disjoint variable violation %s %s", a, b)
			}
			for x := range av {
				for y := range bv {
					needed[[2]string{x, y}] = true
					needed[[2]string{y, x}] = true
				}
			}
		}
		res := substitute(st.expr, subst)
		*stack = append(*stack, res)
		return nil
	default:
		return fmt.Errorf("bad statement kind %s", st.kind)
	}
}

func substitute(expr []string, subst map[string][]string) []string {
	out := []string{expr[0]}
	for _, tok := range expr[1:] {
		if rep, ok := subst[tok]; ok {
			out = append(out, rep[1:]...)
		} else {
			out = append(out, tok)
		}
	}
	return out
}

func (db *Database) lookupSubstitution(v string, subst map[string][]string) ([]string, bool) {
	if expr, ok := subst[v]; ok {
		return expr, true
	}
	if st, ok := db.activeF[v]; ok {
		return append([]string{}, st.expr...), true
	}
	return nil, false
}

func exprEqual(a, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func (db *Database) varsIn(expr []string) map[string]bool {
	m := map[string]bool{}
	for _, tok := range expr[1:] {
		if db.isVarToken(tok) {
			m[tok] = true
		}
	}
	return m
}

func intersects(a, b map[string]bool) bool {
	for k := range a {
		if b[k] {
			return true
		}
	}
	return false
}

func isValidLabel(s string) bool {
	if s == "" {
		return false
	}
	for _, r := range s {
		if !(r == '-' || r == '_' || r == '.' || r == '\'' || (r >= '0' && r <= '9') || (r >= 'A' && r <= 'Z') || (r >= 'a' && r <= 'z')) {
			return false
		}
	}
	return true
}

func (db *Database) isVarActive(v string) bool {
	return db.activeVars[v] > 0
}

func (db *Database) isVarToken(v string) bool {
	return db.allVars[v]
}

func isWhitespace(b byte) bool {
	switch b {
	case ' ', '\t', '\n', '\r', '\f':
		return true
	default:
		return false
	}
}

func isAllowedChar(b byte) bool {
	if b == '\t' || b == '\n' || b == '\f' || b == '\r' {
		return true
	}
	return b >= 32 && b <= 126
}

func isKeyword(second byte) bool {
	switch second {
	case '(', ')', '[', ']', 'c', 'v', 'd', 'f', 'e', 'a', 'p', '=', '.', '{', '}':
		return true
	default:
		return false
	}
}

func (p *Parser) pushFile(path string) error {
	abs, err := filepath.Abs(path)
	if err != nil {
		return err
	}
	data, err := os.ReadFile(abs)
	if err != nil {
		return err
	}
	for i, b := range data {
		if !isAllowedChar(b) {
			return fmt.Errorf("%s contains non-printable ASCII character at offset %d", abs, i)
		}
	}
	ctx := &FileContext{
		path:            abs,
		dir:             filepath.Dir(abs),
		data:            data,
		pos:             0,
		line:            1,
		col:             1,
		afterWhitespace: true,
		blockDepth:      0,
	}
	p.stack = append(p.stack, ctx)
	return nil
}

func (p *Parser) currentFile() *FileContext {
	return p.stack[len(p.stack)-1]
}

func (p *Parser) isOnStack(path string) bool {
	for _, ctx := range p.stack {
		if ctx.path == path {
			return true
		}
	}
	return false
}

func (p *Parser) nextToken() (*Token, error) {
	p.lastComment = false
	for {
		if len(p.stack) == 0 {
			return nil, io.EOF
		}
		ctx := p.currentFile()
		if _, err := ctx.skipWhitespace(); err != nil {
			return nil, err
		}
		if ctx.pos >= len(ctx.data) {
			if ctx.blockDepth != 0 {
				return nil, fmt.Errorf("%s:%d:%d: unclosed ${ ... $} block", ctx.path, ctx.line, ctx.col)
			}
			p.stack = p.stack[:len(p.stack)-1]
			continue
		}
		ch := ctx.data[ctx.pos]
		if !ctx.afterWhitespace {
			return nil, fmt.Errorf("%s:%d:%d: missing whitespace between tokens", ctx.path, ctx.line, ctx.col)
		}
		if ch == '$' {
			if ctx.pos+1 >= len(ctx.data) {
				return nil, fmt.Errorf("%s:%d:%d: dangling $ at end of file", ctx.path, ctx.line, ctx.col)
			}
			second := ctx.data[ctx.pos+1]
			if !isKeyword(second) {
				return nil, fmt.Errorf("%s:%d:%d: invalid keyword $%c", ctx.path, ctx.line, ctx.col, second)
			}
			tok := &Token{value: "$" + string(second), file: ctx.path, line: ctx.line, col: ctx.col}
			ctx.pos += 2
			ctx.col += 2
			ctx.afterWhitespace = false
			if tok.value == "$(" {
				if err := ctx.skipComment(); err != nil {
					return nil, err
				}
				p.lastComment = true
				if ctx.pos < len(ctx.data) {
					if !isWhitespace(ctx.data[ctx.pos]) {
						return nil, fmt.Errorf("%s:%d:%d: missing whitespace after comment", ctx.path, ctx.line, ctx.col)
					}
				}
				ctx.afterWhitespace = true
				continue
			}
			return tok, nil
		}
		startLine := ctx.line
		startCol := ctx.col
		var sb strings.Builder
		for ctx.pos < len(ctx.data) {
			b := ctx.data[ctx.pos]
			if isWhitespace(b) {
				break
			}
			if b == '$' {
				return nil, fmt.Errorf("%s:%d:%d: token contains '$'", ctx.path, startLine, startCol)
			}
			sb.WriteByte(b)
			ctx.pos++
			ctx.col++
		}
		ctx.afterWhitespace = false
		return &Token{value: sb.String(), file: ctx.path, line: startLine, col: startCol}, nil
	}
}

func (ctx *FileContext) skipWhitespace() (bool, error) {
	consumed := false
	for ctx.pos < len(ctx.data) {
		b := ctx.data[ctx.pos]
		if !isWhitespace(b) {
			break
		}
		consumed = true
		switch b {
		case '\n':
			ctx.pos++
			ctx.line++
			ctx.col = 1
		case '\r':
			ctx.pos++
			if ctx.pos < len(ctx.data) && ctx.data[ctx.pos] == '\n' {
				ctx.pos++
			}
			ctx.line++
			ctx.col = 1
		case '\f':
			ctx.pos++
			ctx.line++
			ctx.col = 1
		default:
			ctx.pos++
			ctx.col++
		}
	}
	if consumed {
		ctx.afterWhitespace = true
	}
	return consumed, nil
}

func (ctx *FileContext) skipComment() error {
	for {
		if ctx.pos >= len(ctx.data) {
			return fmt.Errorf("%s:%d:%d: unclosed comment", ctx.path, ctx.line, ctx.col)
		}
		b := ctx.data[ctx.pos]
		if b == '$' {
			if ctx.pos+1 >= len(ctx.data) {
				return fmt.Errorf("%s:%d:%d: unclosed comment", ctx.path, ctx.line, ctx.col)
			}
			next := ctx.data[ctx.pos+1]
			if next == '(' {
				return fmt.Errorf("%s:%d:%d: comments may not contain '$( or $)'", ctx.path, ctx.line, ctx.col)
			}
			if next == ')' {
				ctx.pos += 2
				ctx.col += 2
				return nil
			}
		}
		switch b {
		case '\n':
			ctx.pos++
			ctx.line++
			ctx.col = 1
		case '\r':
			ctx.pos++
			if ctx.pos < len(ctx.data) && ctx.data[ctx.pos] == '\n' {
				ctx.pos++
			}
			ctx.line++
			ctx.col = 1
		case '\f':
			ctx.pos++
			ctx.line++
			ctx.col = 1
		default:
			ctx.pos++
			ctx.col++
		}
	}
}

func (p *Parser) errorf(tok *Token, format string, args ...interface{}) error {
	return fmt.Errorf("%s:%d:%d: "+format, append([]interface{}{tok.file, tok.line, tok.col}, args...)...)
}
