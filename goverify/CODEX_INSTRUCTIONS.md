# Instructions for Codex: Fixing goverify

**Date:** 2025-10-07
**Context:** Unit test suite updated after spec investigation
**Goal:** Update goverify to pass all 36 unit tests

---

## Test Suite Changes

### What Changed:

**Test 17 (UPDATED):**
- **Old:** Include inside block (not outermost scope) → expect REJECT
- **New:** Include scope violation (use included content outside block) → expect REJECT
- **File:** `test17_include_scope_violation.mm`
- **Why:** metamath.exe accepts includes inside blocks but scopes them

**Test 18 (UPDATED):**
- **Old:** Comment in statement → expect REJECT
- **New:** Missing whitespace after comment → expect REJECT
- **File:** `test18_missing_whitespace_after_comment.mm`
- **Why:** Comments ARE whitespace (allowed in statements per metamath.exe)

**Test 28 (UPDATED):**
- **Old:** Include inside block (duplicate of Test 17)
- **New:** Self-include → expect REJECT
- **File:** `test28_self_include.mm`
- **Why:** Self-include causes duplicate declarations (not ignored)

### Tests 29-36:
No changes - these were correct already.

---

## What goverify Needs to Implement

### 1. Include Statement Scoping (Tests 17, 28)

**Required behavior:**

```go
// When processing $[ file.mm $]
if insideBlock {
    // Include is allowed, but content is scoped to this block
    includeFile(path, currentScope)
} else {
    // Include at outermost scope
    includeFile(path, globalScope)
}
```

**Test 17:** Include inside block, then use outside block → should REJECT
```metamath
${
  $[ /tmp/inner.mm $]
  // Can use inner.mm content HERE
$}
// Cannot use inner.mm content HERE (out of scope)
th $p |- y $= wy ax-inner $.  ← Should fail: symbol not active
```

**Test 28:** Self-include → should REJECT
```metamath
$[ THIS_FILE.mm $]  ← Causes duplicate declarations
```

**Implementation notes:**
- Track current scope depth during parsing
- Mark included symbols with their scope level
- When referencing a symbol, check if it's active in current scope
- Self-include: check if included path == current file path → reject OR allow and let duplicates error

---

### 2. Comment Whitespace Rules (Test 18)

**Required behavior:**

```go
// After parsing $( comment $)
// The closing $) MUST be followed by whitespace
if !nextCharIsWhitespace() && !isEOF() {
    return error("keyword must be followed by whitespace")
}
```

**Test 18:** No space after comment → should REJECT
```metamath
$( comment $)wf $f wff x $.  ← No space after $)
```

**Implementation notes:**
- Comments themselves can appear anywhere (they ARE whitespace)
- But the `$)` token must be followed by whitespace
- This is a tokenization rule, not a comment-specific rule

---

### 3. Reference Implementation Behavior

**Key findings from metamath.exe testing:**

| Feature | Spec Says | metamath.exe Does | goverify Should Do |
|---------|-----------|-------------------|-------------------|
| Include inside block | "Should only exist at outermost" | Accepts (scopes) | Accept + scope |
| Comment in statement | Not specified | Accepts (whitespace) | Accept |
| Self-include | Not specified | Rejects (duplicates) | Reject |

**Philosophy:** Follow metamath.exe (reference implementation), not just spec interpretation.

---

## Testing goverify

### Current Status (before fixes):
- **35/36 tests passing (97.2%)**
- **Only Test 36 partial** (whitespace in compressed proof - accepts but doesn't warn)

### After These Fixes:
All 36 tests should pass (100%)!

### How to Test:

```bash
cd /home/zar/claude/hyperon/metamath/metamath-test/unit-tests

# Test individual files
goverify test17_include_scope_violation.mm  # Should reject
goverify test18_missing_whitespace_after_comment.mm  # Should reject
goverify test28_self_include.mm  # Should reject

# Or run full test suite (if test runner updated to use .mm files)
```

---

## Detailed Test Descriptions

### Test 17: Include Scope Violation

**What to test:**
```metamath
$c wff |- $.
$v x $.
wx $f wff x $.

${
  $[ /tmp/inner_test17.mm $]  // Contains: $v y $. wy $f wff y $. ax-inner $a |- y $.
  // ax-inner is ACTIVE here
$}

// ax-inner is NOT ACTIVE here
th2 $p |- y $= wy ax-inner $.  ← Should fail with "symbol not active"
```

**Expected error:**
- "This math symbol is not active"
- OR "The variable \"y\" does not appear in an active \"$f\" statement"

**Implementation check:**
- Does goverify track scope for included symbols?
- Does it reject symbols used outside their scope?

---

### Test 18: Missing Whitespace After Comment

**What to test:**
```metamath
$c wff $.
$v x $.
$( No space after comment close $)wf $f wff x $.
                                  ^^^ No space here!
```

**Expected error:**
- "A keyword must be followed by white space"
- OR "Missing whitespace after token"

**Implementation check:**
- Does goverify tokenizer enforce whitespace after $) ?
- Does it distinguish between:
  - `$)` (comment close token) - must have whitespace after
  - Content inside comments - can be anything

---

### Test 28: Self-Include

**What to test:**
```metamath
$c wff $.
$[ /home/zar/claude/hyperon/metamath/metamath-test/unit-tests/test28_self_include.mm $]
```

**Expected error:**
- "This symbol has already been declared in this scope"
- OR "Circular include detected"
- OR "Self-include not allowed"

**Implementation check:**
- Does goverify detect when included file path == current file path?
- OR does it naturally error due to duplicate declarations when file is read twice?

---

## Background Documents

For context on why these changes were made:

1. **INCLUDE_SEMANTICS_INVESTIGATION.md**
   - Tests showing metamath.exe behavior
   - Include inside block = scoped (not ignored)
   - Self-include = error (not ignored)

2. **SPEC_DIVERGENCES.md**
   - Documents differences between spec and implementation
   - For future discussion with Metamath Google Groups
   - Philosophy: follow reference implementation

3. **GPT5_EVALUATION_SUMMARY.md**
   - Analysis of GPT-5's suggestions
   - Where GPT-5 was right/wrong
   - Why we tested against metamath.exe

---

## Expected Outcome

After implementing these fixes, goverify should achieve:

**36/36 unit tests passing (100%)**

This would make goverify fully compliant with the metamath.exe reference implementation on all known edge cases!

---

## Questions?

See:
- Full test files: `/home/zar/claude/hyperon/metamath/metamath-test/unit-tests/test*.mm`
- Test catalogue: `/home/zar/claude/hyperon/metamath/metamath-test/unit-tests/UNIT_TESTS_CATALOGUE.md`
- Investigation docs: `/home/zar/claude/hyperon/metamath/metamath-test/*.md`

---

**Good luck! The test suite is comprehensive and based on empirical testing with metamath.exe. These fixes will make goverify rock-solid! 🚀**
