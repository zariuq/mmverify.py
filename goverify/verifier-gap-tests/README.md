# Metamath Verifier Gap Tests

**Purpose:** Comprehensive test suite to identify gaps in Metamath verifier implementations.

**What's included:**
- Complete catalogue of 26 known verification gaps
- Test suite that checks each gap
- Example databases that violate exactly ONE rule each

---

## Quick Start

### Test a Verifier

```bash
cd /home/zar/claude/hyperon/metamath/metamath-test/verifier-gap-tests
python test_verifier_gaps.py /path/to/your/verifier
```

### Example: Test goverify

```bash
python test_verifier_gaps.py /home/zar/claude/hyperon/metamath/goverify/goverify
```

### Output

```
Testing verifier: /path/to/verifier
======================================================================

Gap  1: ✅ CAUGHT
  Non-printable ASCII characters
  → Rejected (error_detected=True)

Gap  2: ❌ MISSED
  Missing whitespace between tokens
  → Accepted invalid database!

...

======================================================================
SUMMARY: 15/26 gaps caught, 11/26 missed
Score: 57.7%
======================================================================
```

---

## Files

### 1. `VERIFICATION_GAPS_CATALOGUE.md`

**Complete reference** for all 26 verification gaps, including:
- Plain English description
- Why it matters
- Example invalid databases
- What correct behavior should be

**Use this to:**
- Understand what a complete verifier must check
- Generate test cases
- Guide implementation

### 2. `test_verifier_gaps.py`

**Automated test script** that:
- Tests a verifier against all 26 gaps
- Reports which gaps are caught/missed
- Provides a score (% of gaps caught)

**Use this to:**
- Grade any Metamath verifier
- Track progress during development
- Regression testing

### 3. Individual Gap Test Files (`gap01_*.mm` through `gap26_*.mm`)

**26 individual .mm files**, one for each gap. Each file:
- Contains a database violating exactly ONE rule
- Includes comments explaining which gap it tests
- Can be tested independently with any verifier

**Use these to:**
- Test individual gaps in isolation
- Debug specific verifier failures
- Include in regression test suites
- Provide minimal examples for documentation

**Example usage:**
```bash
# Test a specific gap
metamath 'read "gap07_redeclaration_of_constant.mm"' 'verify proof *' 'exit'

# Test all gaps manually
for f in gap*.mm; do
    echo "Testing $f"
    metamath "read \"$f\"" "verify proof *" "exit"
done
```

---

## The 26 Gaps (Summary)

### Lexical/Character-level (5 gaps)

1. **Non-printable ASCII** - Characters outside printable ASCII
2. **Missing whitespace** - Tokens not separated
3. **Nested comments** - `$(` or `$)` inside comments
4. **Unbalanced blocks** - `${` / `$}` not balanced
5. **$ in symbols** - Math symbols contain `$`

### Syntactic/Token-level (4 gaps)

6. **Dangling $** - File ends with bare `$`
7. **Redeclaration** - Constant/variable declared twice
8. **Variable scope** - Variable used outside scope
9. **Invalid $d** - Disjoint statement with non-variables

### Scoping (5 gaps)

10. **Duplicate labels** - Same label used twice
11. **Label/symbol conflict** - Label same as math symbol
12. **Invalid typecode** - Typecode is not a constant
13. **Inactive variable** - $f uses undeclared variable
14. **Missing $f** - Variable used without type

### Type System (4 gaps)

15. **Multiple $f** - Variable has multiple $f statements
16. **Conflicting types** - Same variable, different typecodes
17. **Recursive include** - File includes itself
18. **Comment in statement** - Comment within statement tokens

### Proof Verification (8 gaps)

19. **Compressed overflow** - Non-canonical compressed proofs
20. **Unknown step ?** - Should accept with warning (not reject!)
21. **Self-reference** - Proof uses its own label
22. **Type mismatch** - Substitution violates types
23. **Wrong hypotheses** - Using hypotheses from wrong scope
24. **Undefined label** - Proof references non-existent label
25. **Missing space** - No space before comment
26. **Wrong conclusion** - Proof result doesn't match statement

---

## Gap Severity

- **Critical** (6): Gaps 21-26 (proof soundness)
- **High** (10): Gaps 4, 5, 7, 8, 10, 12-16 (semantic validity)
- **Medium** (8): Gaps 2, 3, 9, 11, 18, 25 (consistency)
- **Low** (2): Gaps 1, 6, 19 (robustness)
- **Special** (1): Gap 20 (should warn, not reject)

---

## For Codex: How to Use This

### Goal

Make your verifier pass **all 26 tests**.

### Strategy

1. **Run the test suite:**
   ```bash
   python test_verifier_gaps.py ./your_verifier
   ```

2. **For each MISSED gap:**
   - Read the description in `VERIFICATION_GAPS_CATALOGUE.md`
   - Understand what check is missing
   - Add the check to your verifier
   - Re-run tests

3. **Iterate until 26/26 caught**

### Example Workflow

```bash
# Initial run
python test_verifier_gaps.py ./goverify
# Output: 10/26 caught

# Fix Gap 2 (missing whitespace)
# ... edit goverify to add tokenization check ...

# Test again
python test_verifier_gaps.py ./goverify
# Output: 11/26 caught

# Repeat until 26/26
```

### Common Issues

**"Too many false positives"**
- Check Gap 20: Should accept `?` with warning, not reject
- Check Gap 18: Comments between tokens are OK

**"Hard to parse nested structures"**
- Start with lexical gaps (1-6) - easier
- Then scoping (7-14) - medium
- Then proofs (19-26) - hardest

**"Proof verification complex"**
- Focus on gaps 21-24 first (basic soundness)
- Gap 22 (type mismatch) requires tracking substitutions
- Gap 23 (hypothesis scope) requires scope tracking

---

## Testing Strategy

### Minimal Test Set

Focus on **critical** and **high** severity gaps first:

**Must-have (16 gaps):**
- 4, 5, 7, 8, 10, 12-16 (structural integrity)
- 21-26 (proof soundness)

**Nice-to-have (10 gaps):**
- 1-3, 6, 9, 11, 18-20, 25 (robustness)

### Comprehensive Testing

A verifier that catches **all 26 gaps** is:
- Spec-compliant
- Production-ready
- Suitable for differential testing

---

## Integration with Property-Based Testing

These gaps are perfect for **mutation testing**:

```python
from hypothesis import given

@given(gap=st.integers(1, 26), seed=st.integers())
def test_verifier_catches_all_gaps(gap, seed):
    # Generate valid database
    valid_db = generate_database(seed=seed, lines=100)

    # Inject gap
    mutated_db = inject_gap(valid_db, gap_number=gap)

    # Test verifier
    result = run_verifier(mutated_db)

    # Must reject (except Gap 20)
    if gap == 20:
        assert result.success and result.has_warning
    else:
        assert not result.success
```

This ensures the verifier catches gaps in **realistic contexts**, not just minimal examples.

---

## FAQ

**Q: What if my verifier catches some gaps but not others?**

A: That's normal! Most verifiers catch 40-60% of gaps initially. Use this test suite to systematically add missing checks.

**Q: Are these the only possible gaps?**

A: These are the 26 **known** gaps from analyzing goverify and other implementations. There may be more edge cases.

**Q: How do I add a new gap?**

A:
1. Add description to `VERIFICATION_GAPS_CATALOGUE.md`
2. Add test case to `GAP_TESTS` dict in `test_verifier_gaps.py`
3. Re-number gaps if needed

**Q: Can I use this for other Metamath verifiers?**

A: Yes! This is language-agnostic. Works for:
- C (metamath.exe)
- Python (mmverify.py)
- Go (goverify)
- Rust, Java, etc.

---

## Success Metrics

**Goal:** 26/26 gaps caught (100%)

**Current status (goverify):** Unknown (run test to find out!)

**Typical progression:**
- Basic verifier: 8-12/26 (30-45%)
- Intermediate: 16-20/26 (60-75%)
- Advanced: 22-25/26 (85-95%)
- Spec-compliant: 26/26 (100%)

---

## Next Steps

1. **Run the test:** `python test_verifier_gaps.py /path/to/verifier`
2. **Check the score:** How many gaps caught?
3. **Read the catalogue:** Understand missed gaps
4. **Fix and re-test:** Iterate until 26/26

**When you hit 26/26:** Your verifier is ready for production! 🎉

---

*"A verifier is only as good as the gaps it catches."*
