package main

import (
	"errors"
	"flag"
	"fmt"
	"io"
	"math"
	"os"
	"path/filepath"
	"strings"
)

type (
	Label      = string
	Variable   = string
	Typecode   = string
	Expression = []string
	Proof      = []string
	DVPair     = [2]Variable
)

const (
	initialProofCap = 16
	initialExprCap  = 8
)

type ErrCode string

const (
	EParse        ErrCode = "parse_error"
	EIncludeCycle ErrCode = "include_cycle"
	ELabelDup     ErrCode = "label_duplicate"
	EDVViolation  ErrCode = "dv_violation"
	EProof        ErrCode = "proof_error"
	EWhitespace   ErrCode = "whitespace"
)

type VError struct {
	Code ErrCode
	File string
	Line int
	Col  int
	Msg  string
}

func (e *VError) Error() string {
	if e.File == "" {
		return fmt.Sprintf("%s", e.Msg)
	}
	return fmt.Sprintf("%s:%d:%d: %s", e.File, e.Line, e.Col, e.Msg)
}

func newVError(code ErrCode, file string, line, col int, format string, args ...interface{}) *VError {
	return &VError{
		Code: code,
		File: file,
		Line: line,
		Col:  col,
		Msg:  fmt.Sprintf(format, args...),
	}
}

// TABLE OF CONTENTS
// ═══════════════════════════════════════════════════════════════
// 1. Core Data Structures
// 2. Main Entry Point
// 3. Frame Management
// 4. Statement Parsing
// 5. Proof Verification
// 6. Utility Functions
// 7. Parsing & Include Resolution
// ═══════════════════════════════════════════════════════════════

// ═══════════════════════════════════════════════════════════════
// SECTION: Core Data Structures
// ═══════════════════════════════════════════════════════════════

type Statement struct {
	kind       string
	label      Label
	expr       Expression
	proof      Proof
	fHyps      []Label
	eHyps      []Label
	hyps       []Label
	dvPairs    []DVPair
	incomplete bool
}

type Frame struct {
	vars      []Variable
	floating  []*Statement
	essential []*Statement
	dv        map[DVPair]bool
}

// Database stores the full verifier state for the current Metamath file.
// INVARIANTS:
//   - frameStack is never empty (the first frame is the global frame)
//   - constants ∩ allVars = ∅ (a symbol is either a constant or a variable)
//   - mathSymbols = constants ∪ allVars (used for label conflict detection)
//   - activeF contains the active $f statement for each active variable
//   - traceSteps toggles didactic stack tracing (disabled in production)
//   - explain annotates the first failing clause with a spec reference
type Database struct {
	constants   map[Typecode]bool
	allVars     map[Variable]bool
	mathSymbols map[string]bool
	labels      map[Label]*Statement
	frameStack  []*Frame
	activeVars  map[Variable]int
	activeF     map[Variable]*Statement
	warnings    []string
	traceSteps  bool
	explain     bool
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

// Parser drives tokenization across nested include files.
// INVARIANTS:
//   - stack[i].path is always an absolute, canonical path
//   - lastComment is true iff the most recently produced token was a $( ... $) comment
type Parser struct {
	stack       []*FileContext
	lastComment bool
}

func (p *Parser) ensureNotAfterComment(tok *Token) error {
	if p.lastComment {
		p.lastComment = false
		return newVError(EWhitespace, tok.file, tok.line, tok.col, "token must be separated by whitespace after $) (spec §4.4.1)")
	}
	return nil
}

// ═══════════════════════════════════════════════════════════════
// SECTION: Main Entry Point
// ═══════════════════════════════════════════════════════════════

func main() {
	trace := flag.Bool("trace-steps", false, "trace proof stack operations for each step")
	explain := flag.Bool("explain", false, "annotate the first failure with its Metamath spec clause")
	flag.Parse()
	if flag.NArg() != 1 {
		fmt.Println("usage: mmverify [--trace-steps] [--explain] <file.mm>")
		os.Exit(1)
	}
	if err := run(flag.Arg(0), *trace, *explain); err != nil {
		fmt.Fprintf(os.Stderr, "verify failed: %v\n", err)
		os.Exit(1)
	}
	fmt.Println("verification succeeded")
}

func run(path string, traceSteps, explain bool) error {
	db := &Database{
		constants:   map[Typecode]bool{},
		allVars:     map[Variable]bool{},
		mathSymbols: map[string]bool{},
		labels:      map[Label]*Statement{},
		frameStack:  []*Frame{},
		activeVars:  map[Variable]int{},
		activeF:     map[Variable]*Statement{},
		warnings:    []string{},
		traceSteps:  traceSteps,
		explain:     explain,
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
			// Include resolution (Spec §4.1.2): resolve relative paths, detect cycles,
			// and ignore recursive includes instead of erroring like metamath.exe.
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
				// Spec §4.1.2: "A file may include itself...will simply be ignored".
				// The canonical-path comparison detects self-includes and longer cycles
				// (e.g. A → B → A) so we can skip them without recursing forever.
				db.warnings = append(db.warnings, fmt.Sprintf("%s ignored (code=%s)", abs, EIncludeCycle))
				continue
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
				return parser.errorfCode(ELabelDup, tok, "duplicate label '%s'", tok.value)
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

// ═══════════════════════════════════════════════════════════════
// SECTION: Frame Management
// ═══════════════════════════════════════════════════════════════

func (db *Database) pushFrame() {
	fr := &Frame{vars: []Variable{}, floating: []*Statement{}, essential: []*Statement{}, dv: map[DVPair]bool{}}
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

// ═══════════════════════════════════════════════════════════════
// SECTION: Statement Parsing
// ═══════════════════════════════════════════════════════════════

func (db *Database) parseConstants(parser *Parser) error {
	for {
		tok, err := parser.nextToken()
		if err != nil {
			return err
		}
		if tok.value == "$." {
			return nil
		}
		if err := parser.ensureNotAfterComment(tok); err != nil {
			return err
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
		if err := parser.ensureNotAfterComment(tok); err != nil {
			return err
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
	seen := map[Variable]bool{}
	vars := []Variable{}
	for {
		tok, err := parser.nextToken()
		if err != nil {
			return err
		}
		if tok.value == "$." {
			break
		}
		if err := parser.ensureNotAfterComment(tok); err != nil {
			return err
		}
		if !db.isVarActive(tok.value) {
			// SPEC COMPLIANCE: Per §4.2.5, every variable in a $d must be active in the current frame.
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
			fr.dv[DVPair{a, b}] = true
		}
	}
	return nil
}

func (db *Database) parseFloating(label string, parser *Parser) error {
	typeTok, err := parser.nextToken()
	if err != nil {
		return err
	}
	if err := parser.ensureNotAfterComment(typeTok); err != nil {
		return err
	}
	if !db.constants[typeTok.value] {
		return parser.errorf(typeTok, "typecode '%s' is not a declared constant", typeTok.value)
	}
	varTok, err := parser.nextToken()
	if err != nil {
		return err
	}
	if err := parser.ensureNotAfterComment(varTok); err != nil {
		return err
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
		// SPEC COMPLIANCE: Per §4.2.2, $f statements end with exactly two tokens plus $.
		return parser.errorf(endTok, "expected $. after $f statement")
	}
	stmt := &Statement{kind: "$f", label: label, expr: Expression{typeTok.value, varTok.value}}
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

// ═══════════════════════════════════════════════════════════════
// SECTION: Proof Verification
// ═══════════════════════════════════════════════════════════════

func (db *Database) readExpression(endToken string, parser *Parser) (*Statement, error) {
	typeTok, err := parser.nextToken()
	if err != nil {
		return nil, err
	}
	if err := parser.ensureNotAfterComment(typeTok); err != nil {
		return nil, err
	}
	if !db.constants[typeTok.value] {
		return nil, parser.errorf(typeTok, "typecode '%s' is not a declared constant", typeTok.value)
	}
	expr := make(Expression, 0, initialExprCap)
	expr = append(expr, typeTok.value)
	for {
		tok, err := parser.nextToken()
		if err != nil {
			return nil, err
		}
		if tok.value == endToken {
			break
		}
		if err := parser.ensureNotAfterComment(tok); err != nil {
			return nil, err
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

func (db *Database) readProof(parser *Parser) (Proof, error) {
	proof := make(Proof, 0, initialProofCap)
	for {
		tok, err := parser.nextToken()
		if err != nil {
			return nil, err
		}
		if tok.value == "$." {
			break
		}
		if err := parser.ensureNotAfterComment(tok); err != nil {
			return nil, err
		}
		proof = append(proof, tok.value)
	}
	return proof, nil
}

// gatherHyps collects all mandatory hypotheses needed for an assertion.
// Spec anchors: §4.2 (Assertions) and §4.3 (Hypotheses). Mandatory hypotheses
// must be listed in *appearance order*—floating $f entries appear interleaved
// with essential $e entries exactly as they arise in the active frames. This is
// the order that Reverse Polish proof execution (§4.2.6) expects.
func (db *Database) gatherHyps(expr Expression) ([]Label, []Label, error) {
	needed := map[Variable]bool{}
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
	fHyps := []Label{}
	eHyps := []Label{}
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
			vars = append(vars, string(v))
		}
		return nil, nil, fmt.Errorf("missing $f hypotheses for variables: %s", strings.Join(vars, ", "))
	}
	return fHyps, eHyps, nil
}

func (db *Database) gatherDV() []DVPair {
	var res []DVPair
	for _, fr := range db.frameStack {
		for pair := range fr.dv {
			res = append(res, pair)
		}
	}
	return res
}

func (db *Database) explainWrap(err error, clause string) error {
	if err == nil || !db.explain {
		return err
	}
	return fmt.Errorf("%w (violates %s)", err, clause)
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
		return db.explainWrap(db.verifyCompressed(stmt), "spec §§4.1.4, 4.2.6")
	}
	return db.explainWrap(db.verifyNormal(stmt), "spec §4.2.6")
}

func (db *Database) verifyNormal(stmt *Statement) error {
	allowed := map[DVPair]bool{}
	for _, pair := range stmt.dvPairs {
		allowed[pair] = true
		allowed[DVPair{pair[1], pair[0]}] = true
	}
	needed := map[DVPair]bool{}
	stack := []Expression{}
	allowedF := make(map[Label]bool)
	for _, lbl := range stmt.fHyps {
		allowedF[lbl] = true
	}
	allowedE := make(map[Label]bool)
	for _, lbl := range stmt.eHyps {
		allowedE[lbl] = true
	}
	for _, lbl := range stmt.proof {
		st, ok := db.labels[lbl]
		if !ok {
			return fmt.Errorf("unknown label %s", lbl)
		}
		if lbl == stmt.label {
			// CRITICAL SAFETY CHECK: Disallow self-reference which would make
			// any proof succeed trivially by referencing itself.
			return fmt.Errorf("proof may not reference its own label")
		}
		if st.kind == "$f" && !allowedF[st.label] {
			return fmt.Errorf("floating hypothesis %s is not active for this proof", st.label)
		}
		if st.kind == "$e" && !allowedE[st.label] {
			return fmt.Errorf("essential hypothesis %s is not active for this proof", st.label)
		}
		if err := db.applyStep(st, &stack, needed, allowedF, allowedE); err != nil {
			return fmt.Errorf("%s: %w", lbl, err)
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

// verifyCompressed executes a compressed proof.
// Spec anchors: §4.1.4 (compressed proof syntax) and §4.2.6 (stack machine
// semantics). Format is "( labels ) PROOF-STRING" where PROOF-STRING encodes a
// base-20 stream: A–T terminate digits, U–Y extend digits, and Z saves the
// current stack top for reuse.
func (db *Database) verifyCompressed(stmt *Statement) error {
	if len(stmt.proof) < 3 {
		return errors.New("compressed proof missing label block")
	}
	allowed := map[DVPair]bool{}
	for _, pair := range stmt.dvPairs {
		allowed[pair] = true
		allowed[DVPair{pair[1], pair[0]}] = true
	}
	needed := map[DVPair]bool{}
	labelsList := append([]Label{}, stmt.fHyps...)
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
	allowedF := make(map[Label]bool)
	for _, lbl := range stmt.fHyps {
		allowedF[lbl] = true
	}
	allowedE := make(map[Label]bool)
	for _, lbl := range stmt.eHyps {
		allowedE[lbl] = true
	}
	stack := []Expression{}
	saved := []Expression{}
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
				// CRITICAL SAFETY CHECK: Disallow self-reference which would make
				// any proof succeed trivially by referencing itself.
				return fmt.Errorf("proof may not reference its own label")
			}
			if st.kind == "$f" && !allowedF[st.label] {
				return fmt.Errorf("floating hypothesis %s is not active for this proof", st.label)
			}
			if st.kind == "$e" && !allowedE[st.label] {
				return fmt.Errorf("essential hypothesis %s is not active for this proof", st.label)
			}
			if err := db.applyStep(st, &stack, needed, allowedF, allowedE); err != nil {
				return fmt.Errorf("%s: %w", lbl, err)
			}
			continue
		}
		idx := n - len(labelsList)
		if idx >= len(saved) {
			return fmt.Errorf("invalid saved step %d", n)
		}
		tmp := &Statement{kind: "$a", expr: saved[idx], hyps: []Label{}, dvPairs: []DVPair{}}
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

// applyStep applies a single proof step (hypothesis or assertion).
// Spec anchor: §4.2.6 (Reverse Polish proof execution model).
//
// $f/$e hypotheses push their expression onto the stack. For $a/$p assertions:
//  1. Pop the mandatory hypotheses from the stack.
//  2. Build the substitution σ using floating hypotheses.
//  3. Check that essential hypotheses match once σ is applied.
//  4. Enforce disjoint-variable constraints and propagate requirements.
//  5. Push the substituted conclusion expression back to the stack.
//
// This mirrors the Reverse Polish execution model described in spec §4.2.6.
func (db *Database) applyStep(st *Statement, stack *[]Expression, needed map[DVPair]bool, allowedF, allowedE map[Label]bool) error {
	var before []Expression
	if db.traceSteps {
		before = cloneStack(*stack)
		defer func() {
			db.traceStep(st, before, *stack)
		}()
	}
	switch st.kind {
	case "$f":
		*stack = append(*stack, append(Expression{}, st.expr...))
		return nil
	case "$e":
		*stack = append(*stack, append(Expression{}, st.expr...))
		return nil
	case "$a", "$p":
		n := len(st.hyps)
		if len(*stack) < n {
			return errors.New("stack underflow")
		}
		args := (*stack)[len(*stack)-n:]
		*stack = (*stack)[:len(*stack)-n]
		subst := map[Variable]Expression{}
		for i, hlabel := range st.hyps {
			h := db.labels[hlabel]
			arg := append(Expression{}, args[i]...)
			if h.kind == "$f" {
				v := Variable(h.expr[1])
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
			// Check disjoint-variable constraints by examining how σ
			// substitutes each variable from the $d statement.
			aExpr, aOk := db.lookupSubstitution(a, subst)
			bExpr, bOk := db.lookupSubstitution(b, subst)
			if !aOk || !bOk {
				continue
			}
			av := db.varsIn(aExpr) // vars(σ(a))
			bv := db.varsIn(bExpr) // vars(σ(b))
			if intersects(av, bv) {
				return newVError(EDVViolation, "", 0, 0, "disjoint variable violation %s %s", a, b)
			}
			// Record resulting DV requirements: every pair in vars(σ(a)) × vars(σ(b))
			// must be disjoint in the final theorem.
			for x := range av {
				for y := range bv {
					needed[DVPair{x, y}] = true
					needed[DVPair{y, x}] = true
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

func substitute(expr Expression, subst map[Variable]Expression) Expression {
	out := Expression{expr[0]}
	for _, tok := range expr[1:] {
		if rep, ok := subst[Variable(tok)]; ok {
			out = append(out, rep[1:]...)
		} else {
			out = append(out, tok)
		}
	}
	return out
}

func (db *Database) lookupSubstitution(v Variable, subst map[Variable]Expression) (Expression, bool) {
	if expr, ok := subst[v]; ok {
		return expr, true
	}
	if st, ok := db.activeF[v]; ok {
		return append(Expression{}, st.expr...), true
	}
	return nil, false
}

// ═══════════════════════════════════════════════════════════════
// SECTION: Utility Functions
// ═══════════════════════════════════════════════════════════════

func cloneStack(stack []Expression) []Expression {
	out := make([]Expression, len(stack))
	for i, expr := range stack {
		out[i] = append(Expression{}, expr...)
	}
	return out
}

func renderExpression(expr Expression) string {
	return strings.Join(expr, " ")
}

func renderStack(stack []Expression) string {
	if len(stack) == 0 {
		return "[]"
	}
	parts := make([]string, len(stack))
	for i, expr := range stack {
		parts[i] = "[" + renderExpression(expr) + "]"
	}
	return strings.Join(parts, " ")
}

func (db *Database) traceStep(st *Statement, before, after []Expression) {
	if !db.traceSteps {
		return
	}
	label := st.label
	if label == "" {
		label = "(anon)"
	}
	fmt.Fprintf(os.Stderr, "[trace] %s %s\n", st.kind, label)
	fmt.Fprintf(os.Stderr, "        before: %s\n", renderStack(before))
	fmt.Fprintf(os.Stderr, "        after : %s\n", renderStack(after))
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

func (db *Database) varsIn(expr Expression) map[Variable]bool {
	m := map[Variable]bool{}
	for _, tok := range expr[1:] {
		if db.isVarToken(tok) {
			m[Variable(tok)] = true
		}
	}
	return m
}

func intersects(a, b map[Variable]bool) bool {
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

// ═══════════════════════════════════════════════════════════════
// SECTION: Parsing & Include Resolution
// ═══════════════════════════════════════════════════════════════

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
	return newVError(EParse, tok.file, tok.line, tok.col, format, args...)
}

func (p *Parser) errorfCode(code ErrCode, tok *Token, format string, args ...interface{}) error {
	return newVError(code, tok.file, tok.line, tok.col, format, args...)
}
