package main

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
	"unicode"
)

type Statement struct {
	kind  string
	label string
	expr  []string
	hyps  []string // all hypotheses (floating followed by essential)
	fHyps []string // floating hypothesis labels
	eHyps []string // essential hypothesis labels
	dv    [][2]string
	proof []string
}

type Frame struct {
	floating  []string
	essential []string
	dvPairs   [][2]string
}

var (
	constants = map[string]bool{}
	variables = map[string]bool{}
	labels    = map[string]*Statement{}
)

func main() {
	if len(os.Args) != 2 {
		fmt.Println("usage: mmverify <file.mm>")
		os.Exit(1)
	}
	if err := parseFile(os.Args[1]); err != nil {
		fmt.Fprintf(os.Stderr, "verify failed: %v\n", err)
		os.Exit(1)
	}
	fmt.Println("verification succeeded")
}

// tokenizer

type tokenizer struct {
	r *bufio.Reader
}

func newTokenizer(input string) *tokenizer {
	return &tokenizer{bufio.NewReader(strings.NewReader(input))}
}

func (t *tokenizer) next() (string, error) {
	for {
		ch, _, err := t.r.ReadRune()
		if err == io.EOF {
			return "", io.EOF
		}
		if unicode.IsSpace(ch) {
			continue
		}
		if ch == '$' {
			ch2, _, err := t.r.ReadRune()
			if err != nil {
				return "", err
			}
			return "$" + string(ch2), nil
		}
		tok := []rune{ch}
		for {
			ch, _, err := t.r.ReadRune()
			if err == io.EOF {
				return string(tok), nil
			}
			if unicode.IsSpace(ch) {
				return string(tok), nil
			}
			if ch == '$' {
				t.r.UnreadRune()
				return string(tok), nil
			}
			tok = append(tok, ch)
		}
	}
}

// parser and verifier

type fileTok struct {
	tz  *tokenizer
	dir string
}

func parseFile(path string) error {
	frames := []*Frame{{}}
	stack := []fileTok{}
	push := func(p string) error {
		data, err := os.ReadFile(p)
		if err != nil {
			return err
		}
		stack = append(stack, fileTok{tz: newTokenizer(string(data)), dir: filepath.Dir(p)})
		return nil
	}
	if err := push(path); err != nil {
		return err
	}
	next := func() (string, error) {
		for len(stack) > 0 {
			tok, err := stack[len(stack)-1].tz.next()
			if err == io.EOF {
				stack = stack[:len(stack)-1]
				continue
			}
			return tok, err
		}
		return "", io.EOF
	}
	for {
		tok, err := next()
		if err == io.EOF {
			return nil
		}
		if err != nil {
			return err
		}
		switch tok {
		case "$(":
			if err := skipComment(next); err != nil {
				return err
			}
		case "$[":
			fname, err := next()
			if err != nil {
				return err
			}
			end, err := next()
			if err != nil {
				return err
			}
			if end != "$]" {
				return fmt.Errorf("expected $] after include filename")
			}
			curdir := stack[len(stack)-1].dir
			if err := push(filepath.Join(curdir, fname)); err != nil {
				return err
			}
		case "$c":
			for {
				t, err := next()
				if err != nil {
					return err
				}
				if t == "$(" {
					if err := skipComment(next); err != nil {
						return err
					}
					continue
				}
				if t == "$." {
					break
				}
				if strings.HasPrefix(t, "$") {
					return fmt.Errorf("invalid math symbol %s", t)
				}
				constants[t] = true
			}
		case "$v":
			for {
				t, err := next()
				if err != nil {
					return err
				}
				if t == "$(" {
					if err := skipComment(next); err != nil {
						return err
					}
					continue
				}
				if t == "$." {
					break
				}
				if strings.HasPrefix(t, "$") {
					return fmt.Errorf("invalid math symbol %s", t)
				}
				variables[t] = true
			}
		case "$d":
			vars := []string{}
			for {
				t, err := next()
				if err != nil {
					return err
				}
				if t == "$(" {
					if err := skipComment(next); err != nil {
						return err
					}
					continue
				}
				if t == "$." {
					break
				}
				vars = append(vars, t)
			}
			cf := frames[len(frames)-1]
			for i := 0; i < len(vars); i++ {
				for j := i + 1; j < len(vars); j++ {
					cf.dvPairs = append(cf.dvPairs, [2]string{vars[i], vars[j]})
				}
			}
		case "${":
			frames = append(frames, &Frame{})
		case "$}":
			frames = frames[:len(frames)-1]
		default:
			label := tok
			if !isValidLabel(label) {
				return fmt.Errorf("illegal label %s", label)
			}
			stype, err := next()
			if err != nil {
				return err
			}
			switch stype {
			case "$f":
				typecode, _ := next()
				varTok, _ := next()
				if term, _ := next(); term != "$." {
					return fmt.Errorf("expected $. after $f")
				}
				stmt := &Statement{kind: "$f", label: label, expr: []string{typecode, varTok}}
				labels[label] = stmt
				cf := frames[len(frames)-1]
				cf.floating = append(cf.floating, label)
			case "$e":
				typecode, _ := next()
				expr := []string{typecode}
				for {
					t, err := next()
					if err != nil {
						return err
					}
					if t == "$(" {
						if err := skipComment(next); err != nil {
							return err
						}
						continue
					}
					if t == "$." {
						break
					}
					expr = append(expr, t)
				}
				stmt := &Statement{kind: "$e", label: label, expr: expr}
				labels[label] = stmt
				cf := frames[len(frames)-1]
				cf.essential = append(cf.essential, label)
			case "$a":
				typecode, _ := next()
				expr := []string{typecode}
				for {
					t, err := next()
					if err != nil {
						return err
					}
					if t == "$(" {
						if err := skipComment(next); err != nil {
							return err
						}
						continue
					}
					if t == "$." {
						break
					}
					expr = append(expr, t)
				}
				fHyps, eHyps := gatherHyps(frames, expr)
				dv := gatherDVs(frames)
				stmt := &Statement{kind: "$a", label: label, expr: expr, hyps: append(append([]string{}, fHyps...), eHyps...), fHyps: fHyps, eHyps: eHyps, dv: dv}
				labels[label] = stmt
			case "$p":
				typecode, _ := next()
				expr := []string{typecode}
				for {
					t, err := next()
					if err != nil {
						return err
					}
					if t == "$(" {
						if err := skipComment(next); err != nil {
							return err
						}
						continue
					}
					if t == "$=" {
						break
					}
					expr = append(expr, t)
				}
				proof := []string{}
				for {
					t, err := next()
					if err != nil {
						return err
					}
					if t == "$(" {
						if err := skipComment(next); err != nil {
							return err
						}
						continue
					}
					if t == "$." {
						break
					}
					proof = append(proof, t)
				}
				fHyps, eHyps := gatherHyps(frames, expr)
				dv := gatherDVs(frames)
				stmt := &Statement{kind: "$p", label: label, expr: expr, hyps: append(append([]string{}, fHyps...), eHyps...), fHyps: fHyps, eHyps: eHyps, dv: dv, proof: proof}
				labels[label] = stmt
				if err := verify(stmt); err != nil {
					return fmt.Errorf("%s: %v", label, err)
				}
			default:
				return fmt.Errorf("unknown statement type %s", stype)
			}
		}
	}
}

func isValidLabel(s string) bool {
	if s == "" {
		return false
	}
	for _, r := range s {
		if !(unicode.IsLetter(r) || unicode.IsDigit(r) || r == '-' || r == '_' || r == '.') {
			return false
		}
	}
	return true
}

func skipComment(next func() (string, error)) error {
	for {
		t, err := next()
		if err != nil {
			return err
		}
		if t == "$)" {
			return nil
		}
	}
}

func gatherHyps(frames []*Frame, expr []string) (fHyps []string, eHyps []string) {
	varsNeeded := map[string]bool{}
	for _, tok := range expr[1:] {
		if variables[tok] {
			varsNeeded[tok] = true
		}
	}
	for _, fr := range frames {
		for _, elabel := range fr.essential {
			e := labels[elabel]
			for _, tok := range e.expr[1:] {
				if variables[tok] {
					varsNeeded[tok] = true
				}
			}
		}
	}
	for _, fr := range frames {
		for _, flabel := range fr.floating {
			v := labels[flabel].expr[1]
			if varsNeeded[v] {
				fHyps = append(fHyps, flabel)
			}
		}
		eHyps = append(eHyps, fr.essential...)
	}
	return
}

func gatherDVs(frames []*Frame) [][2]string {
	var dv [][2]string
	for _, fr := range frames {
		dv = append(dv, fr.dvPairs...)
	}
	return dv
}

// verification

type substMap map[string][]string

func verify(stmt *Statement) error {
	if len(stmt.proof) > 0 && stmt.proof[0] == "(" {
		return verifyCompressed(stmt)
	}
	return verifyNormal(stmt)
}

func verifyNormal(stmt *Statement) error {
	allowed := map[[2]string]bool{}
	for _, pair := range stmt.dv {
		allowed[[2]string{pair[0], pair[1]}] = true
		allowed[[2]string{pair[1], pair[0]}] = true
	}
	needed := map[[2]string]bool{}
	stack := [][]string{}
	for _, lbl := range stmt.proof {
		st, ok := labels[lbl]
		if !ok {
			return fmt.Errorf("unknown label %s", lbl)
		}
		if err := applyStep(st, &stack, needed); err != nil {
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
			return fmt.Errorf("missing $d %s %s", pair[0], pair[1])
		}
	}
	return nil
}

func verifyCompressed(stmt *Statement) error {
	allowed := map[[2]string]bool{}
	for _, pair := range stmt.dv {
		allowed[[2]string{pair[0], pair[1]}] = true
		allowed[[2]string{pair[1], pair[0]}] = true
	}
	needed := map[[2]string]bool{}
	// Build label list from hypotheses and explicit labels
	labelsList := append(append([]string{}, stmt.fHyps...), stmt.eHyps...)
	idx := 1
	for idx < len(stmt.proof) && stmt.proof[idx] != ")" {
		labelsList = append(labelsList, stmt.proof[idx])
		idx++
	}
	if idx >= len(stmt.proof) || stmt.proof[idx] != ")" {
		return errors.New("unterminated label block in compressed proof")
	}
	idx++
	proofStr := strings.Join(stmt.proof[idx:], "")
	ints := []int{}
	cur := 0
	for _, ch := range proofStr {
		switch {
		case ch == 'Z':
			ints = append(ints, -1)
		case 'A' <= ch && ch <= 'T':
			ints = append(ints, 20*cur+int(ch-'A'))
			cur = 0
		case 'U' <= ch && ch <= 'Y':
			cur = 5*cur + int(ch-'U') + 1
		default:
			return fmt.Errorf("bad compressed proof char %c", ch)
		}
	}
	stack := [][]string{}
	saved := [][]string{}
	for _, n := range ints {
		if n == -1 {
			if len(stack) == 0 {
				return errors.New("nothing to save")
			}
			saved = append(saved, stack[len(stack)-1])
			continue
		}
		if n < len(labelsList) {
			lbl := labelsList[n]
			st, ok := labels[lbl]
			if !ok {
				return fmt.Errorf("unknown label %s", lbl)
			}
			if err := applyStep(st, &stack, needed); err != nil {
				return fmt.Errorf("%s: %v", lbl, err)
			}
			continue
		}
		idx := n - len(labelsList)
		if idx >= len(saved) {
			return fmt.Errorf("invalid saved step %d", n)
		}
		tmp := &Statement{kind: "$a", expr: saved[idx]}
		if err := applyStep(tmp, &stack, needed); err != nil {
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
			return fmt.Errorf("missing $d %s %s", pair[0], pair[1])
		}
	}
	return nil
}

func applyStep(st *Statement, stack *[][]string, needed map[[2]string]bool) error {
	switch st.kind {
	case "$f", "$e":
		*stack = append(*stack, st.expr)
		return nil
	case "$a", "$p":
		n := len(st.hyps)
		if len(*stack) < n {
			return errors.New("stack underflow")
		}
		args := (*stack)[len(*stack)-n:]
		*stack = (*stack)[:len(*stack)-n]
		subst := substMap{}
		for i, hlabel := range st.hyps {
			h := labels[hlabel]
			arg := args[i]
			if h.kind == "$f" {
				v := h.expr[1]
				if ex, ok := subst[v]; ok {
					if !exprEqual(ex, arg) {
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
		for _, pair := range st.dv {
			a, aok := subst[pair[0]]
			b, bok := subst[pair[1]]
			if !aok || !bok {
				continue
			}
			av := varsIn(a)
			bv := varsIn(b)
			if intersects(av, bv) {
				return fmt.Errorf("disjoint variable violation %s %s", pair[0], pair[1])
			}
			for x := range av {
				for y := range bv {
					needed[[2]string{x, y}] = true
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

func substitute(expr []string, subst substMap) []string {
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

func varsIn(expr []string) map[string]bool {
	m := map[string]bool{}
	for _, tok := range expr[1:] {
		if variables[tok] {
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
