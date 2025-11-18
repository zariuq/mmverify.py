# mmverify-utils Unit Tests (MeTTa HE)

**Import-based regression tests** for mmverify-utils.metta functions.

All MeTTa Hyperon Experimental (HE) tests are in this directory with `_he.metta` suffix.
These tests import the actual implementation from `mmverify-utils.metta` (via symlink).

## Test Locations by Implementation

- **MeTTa HE tests** (`*_he.metta`): `/home/zar/claude/hyperon/metamath/mmverify/tests/` (this directory)
- **MM2 tests** (`*.mm2`): `/home/zar/claude/hyperon/MORK/examples/metamath/tests/`
- **PeTTa tests**: (future) Will be in PeTTa directory when implemented

## Running Tests

The tests directory contains a symlink to `../mmverify-utils.metta` so imports work correctly.

```bash
cd /home/zar/claude/hyperon/metamath/mmverify/tests
source /home/zar/miniconda3/bin/activate hyperon

# Run individual tests
metta test_matchc_he.metta
metta test_pop_frame_he.metta
metta test_substitution_he.metta
metta test_treat_hypothesis_he.metta

# Run all unit tests
for f in test_*_he.metta; do echo "=== Running $f ===" && metta $f 2>&1 | grep -E "(Test [0-9]|===|complete)"; done
```

## Test Files

### Integration Tests (7 files)
Tests for complete mmverify functions using real Metamath examples:
- **add_a_he.metta** - Tests add_a (axiom/assertion declarations) and make_assertion
- **add_c_he.metta** - Tests add_c (constant declarations)
- **add_d_he.metta** - Tests add_d (disjoint variable constraints)
- **add_e_he.metta** - Tests add_e (essential hypotheses)
- **add_f_he.metta** - Tests add_f (floating hypotheses)
- **add_v_he.metta** - Tests add_v (variable declarations)
- **push-frame_he.metta** - Tests push-frame (frame stack increment)

### Unit Tests (12 files)

**Core Implementation Tests:**
- **test_treat_hypothesis_he.metta** (10 tests) - Hypothesis processing ($f and $e)
- **test_treat_assertion_he.metta** (10 tests) - Assertion processing ($a and $p) with stack management
- **test_pop_frame_he.metta** (8 tests) - Frame stack management
- **test_make_assertion_he.metta** (12 tests) - Comprehensive make_assertion tests from demo0.mm (consolidated from 4 test files)

**Substitution Tests:**
- **test_substitution_he.metta** (8 tests) - Core substitution functions (apply_subst_tok, add-subst)
- **test_substitution_full_he.metta** (12 tests) - Full substitution with apply_subst and check_subst

**Pattern Matching Tests:**
- **test_remove_patternc_he.metta** (10 tests) - Pattern-based atom removal
- **test_matchc_he.metta** (5 tests) - Collapsed match queries
- **test_match_atom_he.metta** (9 tests) - Match-atom family and collect_lists_by_depth

**Variable and Assignment Tests:**
- **test_var_dv_he.metta** (9 tests) - Variable identification and disjoint variable constraints
- **test_assign_helpers_he.metta** (9 tests) - Mandatory variable assignment helpers

**Utility Tests:**
- **test_list_ops_he.metta** (7 tests) - List operations (to-list, from-list, mappend, flatten-list)
- **helpers_he.metta** (10 tests) - Helper functions (to-list, from-list, mappend, flatten-list, max-atom, collect_lists_by_depth, add_mand_var, assign_f_hyps)

### Status
✅ **102 tests** importing from mmverify-utils.metta
🎯 **All core unit tests complete!** Ready for MM2/PeTTa validation

## Benefits of Import-Based Testing

1. **Regression Testing**: Catches bugs when mmverify-utils.metta is updated
2. **Single Source of Truth**: Tests verify the actual implementation, not copies
3. **Consistency**: Implementation changes automatically tested
4. **Portability**: Same tests can validate MM2/PeTTa implementations

## Key Pattern

```metta
; Import all functions from mmverify-utils.metta
!(import! &self mmverify-utils)

; Test helper
(= (test $actual $expected) (assertEqual $actual $expected))

; Tests follow...
```

## Note on Performance

Import-based tests may run slower than inline tests due to loading all of mmverify-utils.metta. For faster development iteration, use the inline versions in `/home/zar/claude/hyperon/MORK/examples/metamath/tests/`.

## Related Directories

- `/home/zar/claude/hyperon/MORK/examples/metamath/tests/` - Original inline-based tests (faster for development)
- `/home/zar/claude/hyperon/metamath/mmverify/mmverify-utils.metta` - Implementation being tested
