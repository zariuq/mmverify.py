# Metamath Unit Tests

**Purpose:** Comprehensive unit test suite for Metamath databases and verifiers.

Each test is a minimal `.mm` file that violates **exactly ONE rule**, making it easy to understand what correct behavior should be.

---

## 📍 Files Location

```
/home/zar/claude/hyperon/metamath/metamath-test/unit-tests/
├── README.md                          ← You are here
├── UNIT_TESTS_CATALOGUE.md            ← Complete reference (36 tests)
├── run_unit_tests.py                  ← Automated test runner
├── GPT5_GAP_ANALYSIS.md               ← Analysis of additions
├── test01_*.mm                        ← Individual test files
├── test02_*.mm
├── ...
└── test36_*.mm                        ← (36 total .mm files)
```

---

## Quick Start

### Test Any Verifier

```bash
cd /home/zar/claude/hyperon/metamath/metamath-test/unit-tests
python run_unit_tests.py /path/to/your/verifier
```

### Example: Test mmverify (goverify)

```bash
python run_unit_tests.py /home/zar/claude/hyperon/metamath/goverify/mmverify
```

### Output

```
Testing verifier: /path/to/verifier
======================================================================

Test  1: ✅ CAUGHT
  Non-printable ASCII characters
  → Rejected (error_detected=True)

Test  2: ❌ MISSED
  Missing whitespace between tokens
  → Accepted invalid database!

...

======================================================================
SUMMARY: 13/36 tests passed, 23/36 missed
Score: 36.1%
======================================================================
```

---

## Files

### 1. `UNIT_TESTS_CATALOGUE.md`

**Complete reference** for all 36 unit tests:
- Plain English description
- Why each rule matters
- Example invalid databases
- Expected correct behavior

**Use this to:**
- Understand Metamath specification requirements
- Guide verifier implementation
- Learn what can go wrong

### 2. `run_unit_tests.py`

**Automated test runner:**
- Tests any verifier against all 36 tests
- Reports which violations are caught/missed
- Provides a score (% of tests passed)

**Use this to:**
- Grade any Metamath verifier
- Track development progress
- Regression testing

### 3. Individual Test Files (`test01_*.mm` through `test36_*.mm`)

**36 individual `.mm` files**, one per test:
- Minimal database violating exactly ONE rule
- Comments explaining which rule is violated
- Can be tested independently

**Example:**
```bash
# Test a specific violation
metamath 'read "test07_redeclaration_of_constant.mm"' 'verify proof *' 'exit'

# Test all manually
for f in test*.mm; do
    echo "Testing $f"
    your_verifier "$f"
done
```

---

## The 36 Tests (Summary)

### Lexical/Character-level (Tests 1-5)

1. **Non-printable ASCII** - Characters outside printable ASCII
2. **Missing whitespace** - Tokens not separated
3. **Nested comments** - `$(` or `$)` inside comments
4. **Unbalanced blocks** - `${` / `$}` not balanced
5. **$ in symbols** - Math symbols contain `$`

### Syntactic/Token-level (Tests 6-9)

6. **Dangling $** - File ends with bare `$`
7. **Redeclaration** - Constant/variable declared twice
8. **Variable scope** - Variable used outside scope
9. **Invalid $d** - Disjoint statement with non-variables

### Scoping (Tests 10-14)

10. **Duplicate labels** - Same label used twice
11. **Label/symbol conflict** - Label same as math symbol
12. **Invalid typecode** - Typecode is not a constant
13. **Inactive variable** - $f uses undeclared variable
14. **Missing $f** - Variable used without type

### Type System (Tests 15-18)

15. **Multiple $f** - Variable has multiple $f statements
16. **Conflicting types** - Same variable, different typecodes
17. **Include in block** - `$[...]$` not at outermost scope
18. **Comment in statement** - Comment within statement tokens

### Proof Verification (Tests 19-26)

19. **Illegal compressed chars** - Non-[A-Z?] in compressed proof
20. **Unknown step ?** - Should accept with warning (not reject!)
21. **Self-reference** - Proof uses its own label
22. **Type mismatch** - Substitution violates types
23. **Wrong hypotheses** - Using hypotheses from wrong scope
24. **Undefined label** - Proof references non-existent label
25. **Missing space** - No space before comment
26. **Wrong conclusion** - Proof result doesn't match statement

### Disjoint Variable Constraints (Test 27)

27. **DV violation** - Substitution violates $d constraints ⚠️ **CRITICAL**

### Include/File (Tests 28, 31)

28. **Include placement** - Include inside block (not outermost)
31. **Whitespace after comment** - No space after `$)`

### Compressed Proof Integrity (Tests 29-30, 32-36)

29. **Header mismatch** - Compressed proof label-list wrong
30. **? in compressed** - Unknown step in compressed format
32. **Forward reference** - Proof uses later-defined label
33. **Stack underflow** - Compressed index out of bounds
34. **Label/math context** - Label token where math expected
35. **$f scope** - $f not active after block close
36. **Compressed whitespace** - Whitespace in compressed block

---

## Current Baseline: goverify/mmverify

**Score: 13/36 (36.1%)**

**Tests PASSED (13):**
2, 3, 5, 17, 19, 21, 23, 24, 26, 28, 29, 32, 33

**Tests MISSED (23):**
1, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 25, **27**, 30, 31, 34, 35, 36

**Most Critical Gaps:**
- ❌ Test 27: DV constraint enforcement (SOUNDNESS!)
- ❌ Test 7: Redeclaration detection
- ❌ Test 8: Scope violation detection
- ❌ Test 10: Duplicate label detection
- ❌ Test 14: Missing $f detection
- ❌ Test 22: Type mismatch in substitution

---

## For Developers: How to Use This

### Goal: Build a Spec-Compliant Verifier

1. **Run the test suite:**
   ```bash
   python run_unit_tests.py ./your_verifier
   ```

2. **For each MISSED test:**
   - Read `UNIT_TESTS_CATALOGUE.md` for the description
   - Open the corresponding `test##_*.mm` file
   - Understand what check is missing
   - Add the check to your verifier
   - Re-run tests

3. **Iterate until 36/36 passed**

### Priority Order

**Must-have (Critical soundness):**
- Test 27: DV constraints ⚠️
- Tests 21-26: Proof verification

**High priority (Semantic validity):**
- Tests 7, 8, 10, 14: Declarations & scope
- Tests 12-16: Type system

**Medium priority (Robustness):**
- Tests 2-4, 17-18, 28-36: Edge cases

---

## Recent Updates

### 2025-10-07: Expanded to 36 Tests ✅

**Added 10 new tests (27-36)** based on GPT-5 analysis:
- ✅ DV constraint enforcement (Test 27) - **CRITICAL!**
- ✅ Include placement (Test 28)
- ✅ Compressed proof integrity (Tests 29-33)
- ✅ Scoping edge cases (Tests 34-36)

**Fixed existing tests:**
- ✅ Test 17: Include semantics (corrected per spec)
- ✅ Test 19: Compressed alphabet (corrected per spec)

**Renamed:**
- ✅ "Verification gaps" → "Unit tests" (clearer terminology)
- ✅ All files updated accordingly

---

## Implementation Status

### Constructive Generator (`mm_env.py`)

**DV Constraints:**
- ✅ Track $d declarations
- ✅ Record in assertions
- ✅ Check violations with `check_dv_constraints()`

**Variable Ordering:**
- ✅ f_decl_index tracking (bug fixed!)
- ✅ Correct database declaration order
- ✅ 100/100 Hypothesis tests pass

### Test Coverage

- ✅ 36 unit tests
- ✅ 36 individual `.mm` files
- ✅ Automated test runner
- ✅ Comprehensive catalogue

---

*"A verifier is only as good as the violations it catches."*

*"Each unit test is a minimal example of exactly ONE way things can go wrong."*
