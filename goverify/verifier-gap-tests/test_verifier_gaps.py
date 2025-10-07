#!/usr/bin/env python3
"""
Test Suite for Metamath Verifier Gaps

Tests a verifier against all 26 known verification gaps.
Each test creates a database that violates exactly ONE rule.

Usage:
    python test_verifier_gaps.py /path/to/verifier

Output:
    Gap-by-gap report showing which gaps are caught/missed
"""

import subprocess
import tempfile
import os
import sys
from pathlib import Path
from typing import Tuple, Optional


# =============================================================================
# Test Databases for Each Gap
# =============================================================================

GAP_TESTS = {
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
        "name": "Recursive file inclusion",
        "database": "$[ /tmp/recursive_test.mm $]",
        "should_reject": True,
        "error_keywords": ["recursion", "circular", "include", "loop"],
        "setup": lambda: create_recursive_include(),
    },

    18: {
        "name": "Comment in statement",
        "database": """$c wff |- $.
$v x $.
wf $f wff x $.
bad $a $( comment $) |- x $.""",
        "should_reject": True,
        "error_keywords": ["comment", "statement", "token"],
    },

    19: {
        "name": "Compressed proof with leading zeros",
        "database": """$c wff |- $.
$v x $.
wf $f wff x $.
ax $a |- x $.
th $p |- x $= ( ax ) 00001 $.""",
        "should_reject": True,
        "error_keywords": ["compressed", "leading", "zero", "canonical"],
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
}


# =============================================================================
# Helper Functions
# =============================================================================

def create_recursive_include():
    """Create a file that includes itself"""
    path = "/tmp/recursive_test.mm"
    with open(path, 'w') as f:
        f.write(f"$[ {path} $]\n")
    return path


def run_verifier(verifier_path: str, database: str) -> Tuple[bool, str]:
    """
    Run a verifier on a database.

    Returns:
        (success: bool, output: str)
    """
    with tempfile.NamedTemporaryFile(mode='w', suffix='.mm', delete=False) as f:
        f.write(database)
        temp_file = f.name

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

def test_all_gaps(verifier_path: str):
    """
    Test verifier against all gaps.

    Returns:
        Dict of gap_number -> (caught: bool, details: str)
    """
    print(f"Testing verifier: {verifier_path}")
    print("=" * 70)
    print()

    results = {}
    caught_count = 0
    missed_count = 0

    for gap_num in sorted(GAP_TESTS.keys()):
        test = GAP_TESTS[gap_num]
        name = test["name"]
        database = test["database"]
        should_reject = test["should_reject"]
        keywords = test.get("error_keywords", [])

        # Setup if needed
        if "setup" in test:
            test["setup"]()

        # Run verifier
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
            # Should accept (Gap 20: unknown step ?)
            caught = success
            warning_present = check_error_detection(output, keywords)

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

        results[gap_num] = (status, details)

        # Print result
        print(f"Gap {gap_num:2d}: {status}")
        print(f"  {name}")
        print(f"  → {details}")
        print()

    # Summary
    total = len(GAP_TESTS)
    print("=" * 70)
    print(f"SUMMARY: {caught_count}/{total} gaps caught, {missed_count}/{total} missed")
    print(f"Score: {caught_count / total * 100:.1f}%")
    print("=" * 70)

    return results


# =============================================================================
# Main
# =============================================================================

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python test_verifier_gaps.py /path/to/verifier")
        print()
        print("Example:")
        print("  python test_verifier_gaps.py /claude/hyperon/metamath/goverify/goverify")
        sys.exit(1)

    verifier_path = sys.argv[1]

    if not os.path.exists(verifier_path):
        print(f"Error: Verifier not found: {verifier_path}")
        sys.exit(1)

    results = test_all_gaps(verifier_path)

    # Exit with error code if any gaps missed
    missed = sum(1 for status, _ in results.values() if "MISSED" in status)
    sys.exit(0 if missed == 0 else 1)
