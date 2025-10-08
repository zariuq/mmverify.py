#!/usr/bin/env python3
"""
Metamath Unit Test Runner

Tests a verifier against all known unit tests.
Each test is a minimal database that violates exactly ONE rule.

Usage:
    python run_unit_tests.py /path/to/verifier [--from-files]

    --from-files: Load test databases from testNN_*.mm files instead of inline definitions

Output:
    Test-by-test report showing which violations are caught/missed
"""

import subprocess
import tempfile
import os
import sys
import re
from pathlib import Path
from typing import Tuple, Optional, Dict


# =============================================================================
# Unit Test Databases
# Each test violates exactly ONE rule
# =============================================================================

UNIT_TESTS = {
    1: {
        "name": "Non-printable ASCII characters",
        "database": """$c wff |- $.
$c → $.
$v x $.
wf $f wff x $.
ax $a |- x $.""",
        "should_reject": True,
        "error_keywords": ["ascii", "character", "illegal", "invalid"],
    },

    2: {
        "name": "Missing whitespace between tokens",
        "database": """$cwff$c|-.
$vx$.
wf$fwffx$.
ax$a|-x$.""",
        "should_reject": True,
        "error_keywords": ["whitespace", "token", "separator"],
    },

    3: {
        "name": "Nested comment delimiters",
        "database": """$c wff |- $.
$( outer $( nested $) comment $)
$v x $.
wf $f wff x $.
ax $a |- x $.""",
        "should_reject": True,
        "error_keywords": ["comment", "nest", "delimiter"],
    },

    4: {
        "name": "Unbalanced block delimiters",
        "database": """$c wff |- $.
${
  $v x $.
  wf $f wff x $.
$( missing $} $)
ax $a |- x $.""",
        "should_reject": True,
        "error_keywords": ["block", "balance", "brace", "{", "}"],
    },

    5: {
        "name": "Dollar sign in math symbols",
        "database": """$c wff |- $.
$c a$b $.
$v x $.
wf $f wff x $.
ax $a |- x $.""",
        "should_reject": True,
        "error_keywords": ["dollar", "$", "symbol", "constant"],
    },

    6: {
        "name": "Dangling dollar sign at EOF",
        "database": """$c wff |- $.
$v x $.
wf $f wff x $.
$""",
        "should_reject": True,
        "error_keywords": ["dangling", "incomplete", "eof", "token"],
    },

    7: {
        "name": "Redeclaration of constant",
        "database": """$c wff |- $.
$c wff $.
$v x $.
wf $f wff x $.
ax $a |- x $.""",
        "should_reject": True,
        "error_keywords": ["redeclar", "duplicate", "constant"],
    },

    8: {
        "name": "Variable used outside scope",
        "database": """$c wff |- $.
${
  $v x $.
  wf $f wff x $.
$}
bad $a |- x $.""",
        "should_reject": True,
        "error_keywords": ["scope", "inactive", "variable"],
    },

    9: {
        "name": "$d with non-variables",
        "database": """$c wff |- $.
$d wff |- $.""",
        "should_reject": True,
        "error_keywords": ["disjoint", "variable", "constant", "$d"],
    },

    10: {
        "name": "Duplicate labels",
        "database": """$c wff |- $.
$v x $.
dup $f wff x $.
dup $a |- x $.""",
        "should_reject": True,
        "error_keywords": ["duplicate", "label", "redefin"],
    },

    11: {
        "name": "Label conflicts with symbol",
        "database": """$c wff |- $.
$v x $.
wff $f wff x $.""",
        "should_reject": True,
        "error_keywords": ["label", "symbol", "conflict", "namespace"],
    },

    12: {
        "name": "Non-constant typecode",
        "database": """$c wff |- $.
$v x y $.
bad $f x y $.""",
        "should_reject": True,
        "error_keywords": ["typecode", "constant", "variable"],
    },

    13: {
        "name": "$f with undeclared variable",
        "database": """$c wff |- $.
bad $f wff undeclared $.""",
        "should_reject": True,
        "error_keywords": ["undeclared", "variable", "not found"],
    },

    14: {
        "name": "Variable without $f hypothesis",
        "database": """$c wff |- $.
$v x $.
bad $a |- x $.""",
        "should_reject": True,
        "error_keywords": ["$f", "hypothesis", "type", "untyped"],
    },

    15: {
        "name": "Multiple $f for same variable",
        "database": """$c wff class $.
$v x $.
f1 $f wff x $.
f2 $f class x $.""",
        "should_reject": True,
        "error_keywords": ["multiple", "$f", "duplicate", "hypothesis"],
    },

    16: {
        "name": "Conflicting typecodes",
        "database": """$c wff class $.
$v x $.
${
  f1 $f wff x $.
  ${
    f2 $f class x $.
  $}
$}""",
        "should_reject": True,
        "error_keywords": ["typecode", "conflict", "mismatch"],
    },

    17: {
        "name": "Include inside block (not outermost scope)",
        "database": """$c wff |- $.
$v x $.
wx $f wff x $.
${
  $[ inner.mm $]
$}""",
        "should_reject": True,
        "error_keywords": ["include", "outermost", "scope", "block"],
    },

    18: {
        "name": "Missing whitespace after comment",
        "database": """$c wff $.
$v x $.
$( No space after comment close $)wf $f wff x $.""",
        "should_reject": True,
        "error_keywords": ["whitespace", "comment", "token", "keyword"],
    },

    19: {
        "name": "Illegal characters in compressed proof",
        "database": """$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
th $p |- x $= ( ax ) A0B $.""",  # Contains digit '0' - INVALID!
        "should_reject": True,
        "error_keywords": ["compressed", "illegal", "character", "alphabet"],
    },

    20: {
        "name": "Unknown step ? (should accept with warning)",
        "database": """$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
incomplete $p |- x $= ? $.""",
        "should_reject": False,  # Should accept but warn!
        "error_keywords": ["incomplete", "unknown", "?", "warning"],
    },

    21: {
        "name": "Self-referential proof",
        "database": """$c wff |- -> ( ) $.
$v x $.
wf $f wff x $.
evil $p |- ( x -> x ) $= ( evil ) A $.""",
        "should_reject": True,
        "error_keywords": ["circular", "self", "reference", "proof"],
    },

    22: {
        "name": "Typecode mismatch in substitution",
        "database": """$c wff class |- $.
$v x y $.
f1 $f wff x $.
f2 $f class y $.
ax $a |- x $.
bad $p |- y $= f2 ax $.""",
        "should_reject": True,
        "error_keywords": ["typecode", "mismatch", "substitution", "type"],
    },

    23: {
        "name": "Using non-essential hypotheses",
        "database": """$c wff |- $.
$v x $.
wf $f wff x $.
${
  hyp $e |- x $.
  th1 $p |- x $= hyp $.
$}
evil $p |- x $= ( hyp ) A $.""",
        "should_reject": True,
        "error_keywords": ["hypothesis", "scope", "essential", "not found"],
    },

    24: {
        "name": "Undefined label in proof",
        "database": """$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
bad $p |- x $= nosuchlabel $.""",
        "should_reject": True,
        "error_keywords": ["undefined", "label", "not found", "unknown"],
    },

    25: {
        "name": "Missing space before comment",
        "database": """$c wff$.$(comment$)""",
        "should_reject": True,
        "error_keywords": ["whitespace", "token", "comment"],
    },

    26: {
        "name": "Wrong conclusion in proof",
        "database": """$c wff |- $.
$v x y $.
f1 $f wff x $.
f2 $f wff y $.
ax $a |- x $.
bad $p |- y $= f1 ax $.""",
        "should_reject": True,
        "error_keywords": ["conclusion", "mismatch", "proof", "result"],
    },

    # =========================================================================
    # NEW TESTS (27-36) - Added from GPT-5 analysis
    # =========================================================================

    27: {
        "name": "Disjoint variable constraint violation",
        "database": """$c wff -> |- ( ) $.
$v x y z $.
wfx $f wff x $.
wfy $f wff y $.
wfz $f wff z $.
$d x y $.
axxy $a |- ( x -> y ) $.
$( This proof violates $d: substitutes z for both x and y $)
bad $p |- ( z -> z ) $= wfz wfz axxy $.""",
        "should_reject": True,
        "error_keywords": ["disjoint", "constraint", "variable", "$d", "violation"],
    },

    28: {
        "name": "Self-include",
        "database": """$c wff $.
$[ __SELF__ $]""",
        "should_reject": False,  # Spec Section 4.1.2: "will simply be ignored"
        "error_keywords": [],
        "note": "Spec says ignore. metamath.exe rejects (spec divergence).",
        "is_spec_divergence": True,
    },

    29: {
        "name": "Compressed proof header mismatch",
        "database": """$c wff |- $.
$v x $.
wf $f wff x $.
ax1 $a |- x $.
ax2 $a |- x $.
$( Header lists ax1 but proof uses ax2! $)
bad $p |- x $= ( ax1 ) B $.""",
        "should_reject": True,
        "error_keywords": ["compressed", "header", "mismatch", "label"],
    },

    30: {
        "name": "? in compressed proof",
        "database": """$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
incomplete $p |- x $= ( ax ) ? $.""",
        "should_reject": False,  # Should accept with warning
        "error_keywords": ["incomplete", "unknown", "?", "warning"],
    },

    31: {
        "name": "Missing whitespace after comment",
        "database": """$( comment $)$c wff $.""",
        "should_reject": True,
        "error_keywords": ["whitespace", "comment", "token"],
    },

    32: {
        "name": "Forward reference in proof",
        "database": """$c wff |- $.
$v x $.
wf $f wff x $.
early $p |- x $= wf later $.
later $a |- x $.""",
        "should_reject": True,
        "error_keywords": ["forward", "reference", "undefined", "label"],
    },

    33: {
        "name": "Compressed proof stack underflow",
        "database": """$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
$( C tries to pop 3rd item, but stack has only 1 $)
bad $p |- x $= ( ax ) C $.""",
        "should_reject": True,
        "error_keywords": ["stack", "underflow", "compressed", "index"],
    },

    34: {
        "name": "Label token in math context",
        "database": """$c wff |- $.
$v x $.
wf $f wff x $.
$( Using 'wf' where math symbol expected $)
bad $a wf x $.""",
        "should_reject": True,
        "error_keywords": ["label", "math", "token", "context"],
    },

    35: {
        "name": "$f not active after block close",
        "database": """$c wff |- $.
${
  $v x $.
  wf $f wff x $.
$}
$( x and wf are no longer active $)
bad $a |- x $.""",
        "should_reject": True,
        "error_keywords": ["inactive", "scope", "$f", "variable"],
    },

    36: {
        "name": "Whitespace in compressed proof",
        "database": """$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
$( Compressed proof ABC: A=0 (wf), B=1 (ax), C=2 (out of bounds!) $)
th $p |- x $= ( ax ) A
  B
\tC $.""",
        "should_reject": True,  # C references out of bounds (invalid proof)
        "error_keywords": ["compressed", "label", "reference", "range", "out of bounds"],
        "note": "Original test was buggy - intended to test whitespace but proof is actually invalid",
    },

    37: {
        "name": "RPN interleaving of $f and $e in mandatory hypotheses",
        "database": """$c wff |- -> ( ) $.
$v ph ps $.
${
  wph $f wff ph $.
  h1 $e |- ph $.
  wps $f wff ps $.
  ax-test $a |- ( ph -> ps ) $.
$}""",
        "should_reject": False,  # Documents correct behavior
        "error_keywords": [],
        "note": "Mandatory hyps in RPN order must be: wph, h1, wps (appearance order, not 'all $f then $e')",
    },

    38: {
        "name": "Whitespace in valid compressed proof",
        "database": """$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
$( Compressed proof A B with whitespace: spaces, newlines, tabs $)
th $p |- x $= ( ax )   A
  B   $.""",
        "should_reject": False,  # Should accept (whitespace ignored per Spec Section 4.4.2)
        "error_keywords": [],
        "note": "Tests that whitespace between valid compressed proof steps is ignored",
    },
}


# =============================================================================
# File Loading
# =============================================================================

def load_tests_from_files() -> Dict[int, dict]:
    """
    Load test databases from testNN_*.mm files in current directory.

    Returns dict with same structure as UNIT_TESTS.
    """
    tests = {}
    test_dir = Path(__file__).parent

    for test_file in sorted(test_dir.glob("test*.mm")):
        # Extract test number from filename
        match = re.match(r"test(\d+)_.*\.mm$", test_file.name)
        if not match:
            continue

        test_num = int(match.group(1))

        # Read file content
        content = test_file.read_text()

        # Extract expected behavior from first comment
        should_reject = True
        if "Should reject: False" in content:
            should_reject = False

        # Extract test name from comment
        name_match = re.search(r"\$\( Unit Test \d+: (.*?) \$\)", content)
        name = name_match.group(1) if name_match else test_file.stem

        tests[test_num] = {
            "name": name,
            "file_path": str(test_file),
            "should_reject": should_reject,
            "error_keywords": [],  # Can't extract from file
        }

    return tests


# =============================================================================
# Helper Functions
# =============================================================================

def run_verifier(verifier_path: str, database_or_path: str, is_file: bool = False) -> Tuple[bool, str]:
    """
    Run a verifier on a database.

    Args:
        verifier_path: Path to verifier executable
        database_or_path: Either database string or file path
        is_file: True if database_or_path is a file path

    Returns:
        (success: bool, output: str)
    """
    if is_file:
        # Use the file directly
        temp_file = database_or_path
        delete_after = False
    else:
        # Create temp file with database content
        with tempfile.NamedTemporaryFile(mode='w', suffix='.mm', delete=False) as f:
            # Replace __SELF__ placeholder with the temp file path (for self-include test)
            db_text = database_or_path.replace("__SELF__", f.name)
            f.write(db_text)
            temp_file = f.name
        delete_after = True

    try:
        result = subprocess.run(
            [verifier_path, temp_file],
            capture_output=True,
            text=True,
            timeout=5
        )

        success = (result.returncode == 0)
        output = result.stdout + "\n" + result.stderr

        return (success, output)

    except subprocess.TimeoutExpired:
        return (False, "TIMEOUT")
    except FileNotFoundError:
        return (False, f"ERROR: Verifier not found: {verifier_path}")
    finally:
        if delete_after:
            try:
                os.unlink(temp_file)
            except:
                pass


def check_error_detection(output: str, keywords: list) -> bool:
    """Check if output contains any error keywords"""
    output_lower = output.lower()
    return any(keyword.lower() in output_lower for keyword in keywords)


# =============================================================================
# Test Runner
# =============================================================================

def test_all_gaps(verifier_path: str, from_files: bool = False):
    """
    Test verifier against all gaps.

    Args:
        verifier_path: Path to verifier executable
        from_files: If True, load tests from testNN_*.mm files

    Returns:
        Dict of test_number -> (caught: bool, details: str)
    """
    # Load tests
    if from_files:
        tests = load_tests_from_files()
        print(f"Loaded {len(tests)} tests from .mm files")
    else:
        tests = UNIT_TESTS
        print(f"Using {len(tests)} inline test definitions")

    print(f"Testing verifier: {verifier_path}")
    print("=" * 70)
    print()

    results = {}
    caught_count = 0
    missed_count = 0

    for test_num in sorted(tests.keys()):
        test = tests[test_num]
        name = test["name"]
        should_reject = test["should_reject"]
        keywords = test.get("error_keywords", [])

        # Setup if needed (only for inline tests)
        if not from_files and "setup" in test:
            test["setup"]()

        # Run verifier
        if from_files:
            success, output = run_verifier(verifier_path, test["file_path"], is_file=True)
        else:
            database = test["database"]
            success, output = run_verifier(verifier_path, database)

        # Check result
        if should_reject:
            # Should reject
            caught = not success
            error_detected = check_error_detection(output, keywords) if not success else False

            if caught:
                status = "✅ CAUGHT"
                caught_count += 1
                details = f"Rejected (error_detected={error_detected})"
            else:
                status = "❌ MISSED"
                missed_count += 1
                details = "Accepted invalid database!"

        else:
            # Should accept (Test 20, 30, 36: with warning; Test 28: silently)
            caught = success
            warning_present = check_error_detection(output, keywords)

            # If no keywords specified, don't expect a warning (Test 28: self-include)
            if not keywords:
                if caught:
                    status = "✅ CAUGHT"
                    caught_count += 1
                    details = "Accepted (silent, as expected)"
                else:
                    status = "❌ MISSED"
                    missed_count += 1
                    details = "Rejected when should accept silently"
            else:
                # Keywords specified, expect warning
                if caught and warning_present:
                    status = "✅ CAUGHT"
                    caught_count += 1
                    details = "Accepted with warning"
                elif caught:
                    status = "⚠️  PARTIAL"
                    details = "Accepted but no warning"
                else:
                    status = "❌ MISSED"
                    missed_count += 1
                    details = "Rejected valid incomplete proof"

        results[test_num] = (status, details)

        # Print result
        print(f"Test {test_num:2d}: {status}")
        print(f"  {name}")
        print(f"  → {details}")
        print()

    # Summary
    total = len(UNIT_TESTS)
    print("=" * 70)
    print(f"SUMMARY: {caught_count}/{total} tests passed, {missed_count}/{total} missed")
    print(f"Score: {caught_count / total * 100:.1f}%")
    print("=" * 70)

    return results


# =============================================================================
# Main
# =============================================================================

if __name__ == "__main__":
    from_files = False

    if len(sys.argv) < 2:
        print("Usage: python run_unit_tests.py /path/to/verifier [--from-files]")
        print()
        print("Options:")
        print("  --from-files    Load tests from testNN_*.mm files instead of inline definitions")
        print()
        print("Example:")
        print("  python run_unit_tests.py /usr/local/bin/metamath")
        print("  python run_unit_tests.py /claude/hyperon/metamath/goverify/goverify --from-files")
        sys.exit(1)

    verifier_path = sys.argv[1]

    if len(sys.argv) > 2 and sys.argv[2] == "--from-files":
        from_files = True

    if not from_files and not os.path.exists(verifier_path):
        print(f"Error: Verifier not found: {verifier_path}")
        sys.exit(1)

    results = test_all_gaps(verifier_path, from_files=from_files)

    # Exit with error code if any tests failed
    missed = sum(1 for status, _ in results.values() if "MISSED" in status)
    sys.exit(0 if missed == 0 else 1)
