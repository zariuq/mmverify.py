# Metamath Verifier Gaps - Comprehensive Catalogue

**Purpose:** Enumerate every possible way a Metamath verifier can fail to catch invalid input.

**Use case:** Generate "almost valid" databases that fail in exactly ONE way, to test verifier completeness.

---

## Categories

1. **Lexical/Character-level violations** (Gaps 1-5)
2. **Syntactic/Token-level violations** (Gaps 6-9)
3. **Scoping violations** (Gaps 10-14)
4. **Type system violations** (Gaps 15-18)
5. **Proof verification violations** (Gaps 19-24)
6. **Include/File violations** (Gaps 25-26)

---

## Gap 1: Non-printable ASCII Characters

**Description:** File contains characters outside printable ASCII + whitespace

**Valid set:** `[#x20-#x7E] | [\t\n\f\r]`

**Invalid examples:**
- Unicode: `$c → $.` (using U+2192 instead of ASCII `->`)
- Control chars: `$c \x01 $.`
- High ASCII: `$c ñ $.`

**Why it matters:** Different verifiers may treat non-ASCII differently (especially whitespace variants)

**Test database:**
```metamath
$c wff |- $.
$c → $.  ← Unicode arrow (U+2192)
```

**Expected:** Reject with lexical error

---

## Gap 2: Missing Whitespace Between Tokens

**Description:** Keywords not separated by whitespace

**Invalid examples:**
- `$($)` - No space between `$(` and `$)`
- `foo$a|- bar$.` - No space before `$a`, after `|-`, before `$.`
- `$c$v` - Two keywords touching

**Valid:** `$( comment $)`, `foo $a |- bar $.`

**Why it matters:** Tokenizer must properly separate keywords

**Test database:**
```metamath
$cwff$c|-.  ← No spaces
```

**Expected:** Reject with tokenization error

---

## Gap 3: Nested Comment Delimiters

**Description:** Comments contain `$(` or `$)`

**Invalid examples:**
- `$( nested $( comment $) $)`
- `$( has $) inside $)`

**Valid:** `$( comment without delimiters $)`

**Why it matters:** Comment parsing must be non-recursive

**Test database:**
```metamath
$c wff $.
$( outer $( inner $) comment $)
```

**Expected:** Reject with comment nesting error

---

## Gap 4: Unbalanced Block Delimiters

**Description:** `${` and `$}` not balanced within a file

**Invalid examples:**
- `${ ${ $}` - Extra open
- `${ $} $}` - Extra close
- `${ $c wff $.` - No closing `$}`

**Valid:** `${ $c x $. $}` (balanced)

**Why it matters:** Scoping depends on proper block nesting

**Test database:**
```metamath
$c wff $.
${
  $v x $.
$( no closing $} $)
```

**Expected:** Reject with unbalanced block error

---

## Gap 5: Dollar Sign in Math Symbols

**Description:** Math symbols (constants/variables) contain `$`

**Invalid examples:**
- `$c a$b $.` - Constant contains `$`
- `$v x$y $.` - Variable contains `$`

**Valid:** `$c ab $.`, `$v xy $.`

**Why it matters:** `$` is reserved for keywords

**Test database:**
```metamath
$c wff |- $.
$c a$b $.  ← Invalid constant
```

**Expected:** Reject with illegal character in symbol

---

## Gap 6: Dangling Dollar Sign

**Description:** File ends with bare `$` not part of any keyword

**Invalid example:**
```metamath
$c wff $.
$
```

**Valid:** File ends with complete statement

**Why it matters:** Parser must handle EOF correctly

**Test database:**
```metamath
$c wff $.
$v x $.
$
```

**Expected:** Reject with incomplete token

---

## Gap 7: Redeclaration of Constants/Variables

**Description:** Active constant/variable is redeclared, or variable declared as constant (or vice versa)

**Invalid examples:**
- `$c wff $. $c wff $.` - Constant redeclared
- `$v x $. $v x $.` - Variable redeclared (in same scope)
- `$c x $. $v x $.` - Constant declared as variable
- `$v x $. $c x $.` - Variable declared as constant

**Valid:**
- `${ $v x $. $} $v x $.` - OK (different scopes)

**Why it matters:** Symbol namespaces must be consistent

**Test database:**
```metamath
$c wff $.
$c wff $.  ← Redeclaration
```

**Expected:** Reject with redeclaration error

---

## Gap 8: Variables Not Becoming Inactive

**Description:** Variables remain active after their block closes

**Invalid example:**
```metamath
$c wff $.
${
  $v x $.
$}
$( x should be inactive here $)
wf $f wff x $.  ← x is inactive!
```

**Valid:** Variables only used within their scope

**Why it matters:** Scoping rules must be enforced

**Test database:**
```metamath
$c wff $.
${
  $v x $.
  wf $f wff x $.
$}
bad $a wff x $.  ← x inactive here
```

**Expected:** Reject with inactive variable error

---

## Gap 9: $d Statement with Non-Variables or Duplicates

**Description:** `$d` statement contains non-variables, inactive variables, or duplicate symbols

**Invalid examples:**
- `$d wff |- $.` - Constants in $d (should be variables)
- `$d x x $.` - Duplicate variable
- `$d x y $.` (where x not declared) - Inactive variable

**Valid:** `$v x y $. $d x y $.`

**Why it matters:** Disjoint variable constraints only apply to variables

**Test database:**
```metamath
$c wff |- $.
$d wff |- $.  ← Constants in $d
```

**Expected:** Reject with non-variable in $d

---

## Gap 10: Duplicate Labels

**Description:** Same label used for multiple statements

**Invalid examples:**
- `foo $f wff x $. foo $a |- x $.` - Label `foo` used twice

**Valid:** All labels unique

**Why it matters:** Label namespace must be unique

**Test database:**
```metamath
$c wff $.
$v x $.
dup $f wff x $.
dup $a wff x $.  ← Duplicate label
```

**Expected:** Reject with duplicate label error

---

## Gap 11: Label Conflicts with Math Symbols

**Description:** Label has same name as a constant or variable

**Invalid examples:**
- `$c wff $. wff $f wff x $.` - Label `wff` same as constant

**Valid:** Labels in separate namespace from symbols

**Why it matters:** Prevents ambiguity in proofs

**Test database:**
```metamath
$c wff $.
$v x $.
wff $f wff x $.  ← Label same as constant
```

**Expected:** Reject with label/symbol conflict

---

## Gap 12: Non-Constant Typecode

**Description:** Typecode in $f, $e, $a, or $p is not an active constant

**Invalid examples:**
- `$v x y $. foo $f x y $.` - `x` is a variable, not constant
- `foo $f undef y $.` - `undef` not declared

**Valid:** `$c wff $. $v x $. foo $f wff x $.`

**Why it matters:** Typecodes must be from constant namespace

**Test database:**
```metamath
$c wff $.
$v x y $.
bad $f x y $.  ← x is variable, not typecode
```

**Expected:** Reject with invalid typecode

---

## Gap 13: $f Statement with Inactive Variable

**Description:** Variable in $f statement is not active

**Invalid example:**
```metamath
$c wff $.
foo $f wff x $.  ← x never declared
```

**Valid:** `$v x $. foo $f wff x $.`

**Why it matters:** All variables must be declared

**Test database:**
```metamath
$c wff $.
bad $f wff undeclared $.  ← Variable not declared
```

**Expected:** Reject with undeclared variable

---

## Gap 14: Variables Without $f Hypothesis

**Description:** Variable used in $e, $a, or $p without an active $f

**Invalid example:**
```metamath
$c wff |- $.
$v x $.
$( no $f for x $)
bad $a |- x $.  ← x has no type
```

**Valid:**
```metamath
$v x $.
wf $f wff x $.
good $a |- x $.
```

**Why it matters:** All variables must be typed

**Test database:**
```metamath
$c wff |- $.
$v x $.
bad $a |- x $.  ← No $f for x
```

**Expected:** Reject with untyped variable

---

## Gap 15: Multiple $f for Same Variable

**Description:** Variable has more than one active $f statement

**Invalid example:**
```metamath
$c wff class $.
$v x $.
wf1 $f wff x $.
wf2 $f class x $.  ← x already has $f
```

**Valid:** At most one $f per variable (in same scope)

**Why it matters:** Each variable has unique type

**Test database:**
```metamath
$c wff class $.
$v x $.
f1 $f wff x $.
f2 $f class x $.  ← Duplicate $f
```

**Expected:** Reject with multiple $f error

---

## Gap 16: Conflicting Typecodes for Same Variable

**Description:** Variable has different typecodes in different active $f statements (across scopes)

**Invalid example:**
```metamath
$c wff class $.
${
  $v x $.
  f1 $f wff x $.
  ${
    f2 $f class x $.  ← Different typecode!
  $}
$}
```

**Valid:** Same typecode if variable has multiple $f (shouldn't happen, but if it does, must match)

**Why it matters:** Type consistency

**Test database:**
```metamath
$c wff class $.
$v x $.
${
  f1 $f wff x $.
  ${
    f2 $f class x $.  ← Conflicting type
  $}
$}
```

**Expected:** Reject with typecode mismatch

---

## Gap 17: Recursive File Inclusion

**Description:** File includes itself, directly or indirectly

**Invalid example:**
```metamath
$( In test.mm: $)
$[ test.mm $]  ← Includes itself!
```

**Valid:** No circular includes

**Why it matters:** Prevents infinite loops / memory leaks

**Test database:**
Create `test.mm` containing:
```metamath
$[ test.mm $]
```

**Expected:** Reject with circular include error

---

## Gap 18: Comments in Statement Context

**Description:** Comments appear within statements (not between tokens)

**Invalid example:**
```metamath
foo $a $( comment $) |- bar $.
```

This might be parsed as:
- Typecode: `$(`
- Expression: `$( comment $) |- bar`

**Valid:** Comments only between statements

**Why it matters:** Comment handling must be consistent

**Test database:**
```metamath
$c wff |- $.
$v x $.
wf $f wff x $.
bad $a $( oops $) |- x $.  ← Comment in statement
```

**Expected:** Reject or skip comment consistently

---

## Gap 19: Integer Overflow in Compressed Proofs

**Description:** Compressed proof labels use numbers that overflow or have multiple representations

**Invalid examples:**
- Step number > max int
- Leading zeros: `A` vs `01A` (both represent same step)
- `Z` represented as number instead of special code

**Valid:** Canonical representation only

**Why it matters:** Verifiers must agree on step numbering

**Test database:**
```metamath
$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
th $p |- x $= ( ax ) 00001 $.  ← Leading zeros
```

**Expected:** Reject non-canonical compressed proof

---

## Gap 20: Unknown Step `?` Not Handled

**Description:** Proof contains `?` but verifier doesn't skip it appropriately

**Invalid example:**
```metamath
th $p |- x $= ? $.
$( Verifier should warn but continue $)
```

**Valid:** Verifier warns about incomplete proof but doesn't crash

**Why it matters:** Incomplete proofs are valid syntactically

**Test database:**
```metamath
$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
incomplete $p |- x $= ? $.
```

**Expected:** Accept with warning (not reject!)

---

## Gap 21: Self-Referential Proof

**Description:** Proof uses its own label as a step

**Invalid example:**
```metamath
$c wff |- $.
$v x $.
wf $f wff x $.
evil $p |- x $= ( evil ) AB $.  ← Uses own label!
```

**Valid:** Proofs only reference earlier statements

**Why it matters:** Circularity is unsound

**Test database:**
```metamath
$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- ( x -> x ) $.
evil $p |- ( x -> x ) $= ( evil ) A $.  ← Self-ref
```

**Expected:** Reject with circular reference

---

## Gap 22: Typecode Mismatch in Substitution

**Description:** Proof substitutes variable with expression of wrong type

**Invalid example:**
```metamath
$c wff class |- $.
$v x y $.
wfx $f wff x $.
wfy $f class y $.  ← Different typecode!
ax $a |- x $.
bad $p |- y $= wfy ax $.  ← Substitutes wff for class!
```

**Valid:** Substitution preserves typecodes

**Why it matters:** Type safety

**Test database:**
```metamath
$c wff class |- $.
$v x y $.
f1 $f wff x $.
f2 $f class y $.
ax $a |- x $.
bad $p |- y $= f2 ax $.  ← Type mismatch
```

**Expected:** Reject with type error

---

## Gap 23: Using Non-Essential Hypotheses

**Description:** Proof uses hypotheses from another statement's scope

**Invalid example:**
```metamath
$c wff |- $.
$v x $.
wf $f wff x $.
${
  min $e |- x $.
  th1 $p |- x $= min $.
$}
evil $p |- x $= ( min ) A $.  ← Uses th1's hypothesis!
```

**Valid:** Each proof only uses its own mandatory hypotheses

**Why it matters:** Hypotheses are scoped to their statement

**Test database:**
```metamath
$c wff |- $.
$v x $.
wf $f wff x $.
${
  hyp $e |- x $.
  th1 $p |- x $= hyp $.
$}
evil $p |- x $= ( hyp ) A $.  ← hyp not in scope!
```

**Expected:** Reject with hypothesis scope error

---

## Gap 24: Proof Steps Not on Stack

**Description:** Proof references step that doesn't exist or is out of order

**Invalid example:**
```metamath
$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
bad $p |- x $= nosuch $.  ← Label doesn't exist
```

**Valid:** All proof steps reference valid statements

**Why it matters:** Proof integrity

**Test database:**
```metamath
$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
bad $p |- x $= undefined $.  ← No such label
```

**Expected:** Reject with undefined label

---

## Gap 25: Missing Whitespace Before Comment

**Description:** No space between token and `$(`

**Invalid example:**
```metamath
$c wff$.$(comment$)
```

**Valid:** `$c wff $. $( comment $)`

**Why it matters:** Tokenization consistency

**Test database:**
```metamath
$c wff$.$(bad$)
```

**Expected:** Reject with tokenization error

---

## Gap 26: Wrong Conclusion in Proof

**Description:** Proof steps produce different result than stated

**Invalid example:**
```metamath
$c wff |- $.
$v x y $.
wfx $f wff x $.
wfy $f wff y $.
ax $a |- x $.
bad $p |- y $= wfx ax $.  ← Produces x, not y!
```

**Valid:** Proof result matches statement

**Why it matters:** Core verification

**Test database:**
```metamath
$c wff |- $.
$v x y $.
f1 $f wff x $.
f2 $f wff y $.
ax $a |- x $.
bad $p |- y $= f1 ax $.  ← Wrong conclusion
```

**Expected:** Reject with proof verification failure

---

## Summary Table

| Gap | Category | Description | Severity |
|-----|----------|-------------|----------|
| 1 | Lexical | Non-printable chars | Low |
| 2 | Lexical | Missing whitespace | Medium |
| 3 | Lexical | Nested comments | Medium |
| 4 | Syntactic | Unbalanced blocks | High |
| 5 | Lexical | $ in symbols | High |
| 6 | Syntactic | Dangling $ | Low |
| 7 | Scoping | Redeclaration | High |
| 8 | Scoping | Variable scope | High |
| 9 | Syntactic | Invalid $d | Medium |
| 10 | Scoping | Duplicate labels | High |
| 11 | Scoping | Label/symbol conflict | Medium |
| 12 | Type | Invalid typecode | High |
| 13 | Scoping | Inactive variable | High |
| 14 | Type | Missing $f | High |
| 15 | Type | Multiple $f | High |
| 16 | Type | Conflicting types | High |
| 17 | Include | Recursive include | High |
| 18 | Syntactic | Comment in statement | Medium |
| 19 | Proof | Compressed overflow | Low |
| 20 | Proof | Unknown step ? | Special |
| 21 | Proof | Self-reference | Critical |
| 22 | Proof | Type mismatch | Critical |
| 23 | Proof | Wrong hypotheses | Critical |
| 24 | Proof | Undefined label | High |
| 25 | Lexical | Missing space | Medium |
| 26 | Proof | Wrong conclusion | Critical |

---

## Usage for Property-Based Testing

For each gap, generate a database that:
1. Is otherwise completely valid
2. Fails in EXACTLY ONE way (the specified gap)
3. Is reasonably complex (100+ lines)
4. Has the gap hidden among valid content (not obvious)

This tests whether a verifier catches that specific gap.

**Ideal test:**
```python
@given(gap_number=st.integers(1, 26))
def test_verifier_catches_gap(gap_number):
    valid_db = generate_valid_database(lines=100)
    mutated_db = inject_gap(valid_db, gap_number)

    result = run_verifier(mutated_db)

    # Must reject
    assert not result.success, f"Gap {gap_number} not caught!"

    # Must identify the right error
    assert gap_number in result.error_codes
```

This catalogue provides the foundation for comprehensive verifier testing!
