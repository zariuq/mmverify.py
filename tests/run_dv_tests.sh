#!/bin/bash
# Run all DV test files with HE MeTTa and report results

echo "======================================"
echo "DV Test Suite v2.0 - HE MeTTa"
echo "9 comprehensive DV tests"
echo "======================================"
echo ""

cd "$(dirname "$0")"

# Activate conda environment
source /home/zar/miniconda3/bin/activate hyperon

TESTS=(
    "test_dv_01_direct_bad.metta"
    "test_dv_02_different_good.metta"
    "test_dv_03_symmetric_bad.metta"
    "test_dv_04_nested_good.metta"
    "test_dv_05_nested_bad.metta"
    "test_dv_06_threeway_good.metta"
    "test_dv_07_threeway_bad.metta"
    "test_dv_08_no_constraints_good.metta"
    "test_dv_09_fourway_bad.metta"
)

EXPECTED_FAIL=("01" "03" "05" "07" "09")
EXPECTED_PASS=("02" "04" "06" "08")

PASS=0
FAIL=0
UNEXPECTED=0

for test in "${TESTS[@]}"; do
    echo "----------------------------------------"
    echo "Running: $test"
    echo "----------------------------------------"

    # Extract test number
    test_num=$(echo "$test" | grep -oP 'test_dv_\K\d+')

    # Run test and capture output
    output=$(metta "$test" 2>&1)
    exit_code=$?

    # Check if error was produced
    has_error=$(echo "$output" | grep -c "Error.*Disjoint variable violation")

    # Determine expected behavior
    should_fail=0
    for num in "${EXPECTED_FAIL[@]}"; do
        if [ "$test_num" = "$num" ]; then
            should_fail=1
            break
        fi
    done

    # Validate result
    if [ $should_fail -eq 1 ]; then
        if [ $has_error -gt 0 ]; then
            echo "✓ CORRECT: DV violation detected as expected"
            ((PASS++))
        else
            echo "✗ UNEXPECTED: Should have failed but passed!"
            ((UNEXPECTED++))
        fi
    else
        if [ $has_error -eq 0 ]; then
            echo "✓ CORRECT: Test passed as expected"
            ((PASS++))
        else
            echo "✗ UNEXPECTED: Should have passed but failed!"
            echo "$output" | grep "Error"
            ((UNEXPECTED++))
        fi
    fi

    echo ""
done

echo "======================================"
echo "Test Suite Summary"
echo "======================================"
echo "Total tests: ${#TESTS[@]}"
echo "Correct: $PASS"
echo "Unexpected results: $UNEXPECTED"
echo "======================================"

if [ $UNEXPECTED -eq 0 ]; then
    echo "✓ All tests behaved as expected!"
    exit 0
else
    echo "✗ Some tests had unexpected results"
    exit 1
fi
