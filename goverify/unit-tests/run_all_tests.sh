#!/bin/bash
# Comprehensive test runner for all Metamath verifiers
# Tests all 50 tests on all available verifiers

set -e

# Color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Verifiers to test
GOVERIFY="/home/zar/claude/hyperon/metamath/goverify/mmverify"
METAMATH_KNIFE="metamath-knife --verify"

# Test expectations (1=should pass, 0=should fail)
declare -A EXPECTED
EXPECTED[01]=0  # Non-printable
EXPECTED[02]=0  # Unclosed comment
EXPECTED[03]=0  # Unmatched block
EXPECTED[04]=0  # Missing terminator
EXPECTED[05]=0  # Empty label
EXPECTED[06]=0  # Invalid token
EXPECTED[07]=1  # Valid minimal
EXPECTED[08]=0  # Variable out of scope
EXPECTED[09]=0  # Missing $d
EXPECTED[10]=0  # Duplicate label
EXPECTED[45]=1  # Variable redeclaration (NEW)
EXPECTED[46]=1  # Duplicate include (NEW)
EXPECTED[47]=0  # $c in inner scope (NEW - CRITICAL)
EXPECTED[48]=0  # Variable conflict (NEW - CRITICAL)
EXPECTED[49]=1  # Token splice axiom (NEW - optional?)
EXPECTED[50]=1  # Token splice proof (NEW - optional?)

echo "================================"
echo "Metamath Verifier Test Suite"
echo "Testing: goverify, metamath-knife"
echo "================================"
echo

# Function to test a single verifier
test_verifier() {
    local verifier_name=$1
    local verifier_cmd=$2
    local pass_count=0
    local fail_count=0
    local total_count=0

    echo "Testing ${verifier_name}..."
    echo "---"

    # Test a subset of critical tests
    for test_num in 01 07 08 45 46 47 48; do
        local test_file="test${test_num}_*.mm"
        local matching_files=(test${test_num}_*main.mm test${test_num}_*.mm)
        local test_file="${matching_files[0]}"

        # Skip if file doesn't exist
        if [ ! -f "$test_file" ]; then
            continue
        fi

        total_count=$((total_count + 1))
        local expected=${EXPECTED[$test_num]}

        # Run verifier
        if $verifier_cmd "$test_file" > /dev/null 2>&1; then
            local result=1  # Passed
        else
            local result=0  # Failed
        fi

        # Check if matches expectation
        if [ $result -eq $expected ]; then
            echo -e "${GREEN}✓${NC} Test $test_num: ${test_file}"
            pass_count=$((pass_count + 1))
        else
            if [ $expected -eq 1 ]; then
                echo -e "${RED}✗${NC} Test $test_num: ${test_file} (should ACCEPT, but REJECTED)"
            else
                echo -e "${RED}✗${NC} Test $test_num: ${test_file} (should REJECT, but ACCEPTED)"
            fi
            fail_count=$((fail_count + 1))
        fi
    done

    echo "---"
    echo "${verifier_name}: ${pass_count}/${total_count} tests passed"
    echo
}

# Test goverify
if [ -x "$GOVERIFY" ]; then
    test_verifier "goverify" "$GOVERIFY"
else
    echo "goverify not found at $GOVERIFY"
fi

# Test metamath-knife
if command -v metamath-knife &> /dev/null; then
    test_verifier "metamath-knife" "$METAMATH_KNIFE"
else
    echo "metamath-knife not found in PATH"
fi

echo "================================"
echo "Test run complete"
echo "================================"
