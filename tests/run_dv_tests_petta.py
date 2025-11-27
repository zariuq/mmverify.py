#!/usr/bin/env python3
"""
Test driver for mmverify-utils.metta DV checking in PeTTa
Runs comprehensive test suite and reports results

Usage:
    python run_dv_tests_petta.py
    python run_dv_tests_petta.py --verbose
    python run_dv_tests_petta.py --filter "nested"
"""

import subprocess
import sys
import os
import re
from pathlib import Path
from typing import List, Tuple, Optional
import argparse
import time

# ANSI color codes
GREEN = '\033[92m'
RED = '\033[91m'
YELLOW = '\033[93m'
BLUE = '\033[94m'
RESET = '\033[0m'
BOLD = '\033[1m'

class TestResult:
    def __init__(self, name: str, expected_fail: bool, actual_failed: bool,
                 output: str, duration: float):
        self.name = name
        self.expected_fail = expected_fail
        self.actual_failed = actual_failed
        self.output = output
        self.duration = duration
        self.passed = (expected_fail == actual_failed)

class PeTTaTestRunner:
    def __init__(self, verbose: bool = False, filter_pattern: Optional[str] = None):
        self.verbose = verbose
        self.filter_pattern = filter_pattern
        self.tests_dir = Path(__file__).parent
        # PeTTa runner path is relative to tests_dir
        self.petta_runner_path = self.tests_dir.parent.parent.parent / "PeTTa" / "run.sh"
        self.results: List[TestResult] = []

    def find_tests(self) -> List[Path]:
        """Find all test_dv_*.metta files"""
        # Ensure we only pick up _petta.metta files if they exist, otherwise general .metta
        tests_petta = sorted(self.tests_dir.glob("test_dv_*_petta.metta"))
        tests_general = sorted(self.tests_dir.glob("test_dv_*.metta"))
        
        # Prefer _petta specific tests if they exist, otherwise use general ones
        tests = tests_petta if tests_petta else tests_general

        if self.filter_pattern:
            tests = [t for t in tests if self.filter_pattern in t.name]

        return tests

    def should_fail(self, test_path: Path) -> bool:
        """Determine if test should fail based on naming convention"""
        name = test_path.stem
        # Extract test number from name like 'test_dv_01_petta'
        match = re.search(r'test_dv_(\d+)_petta', name)
        if match:
            test_num = int(match.group(1))
            return test_num in {1, 3, 5, 7, 9}
        return False

    def run_test(self, test_path: Path) -> TestResult:
        """Run a single test and capture results"""
        
        test_name = test_path.name
        expected_fail = self.should_fail(test_path)

        if self.verbose:
            print(f"\n{BLUE}Running: {test_name}{RESET}")
            print(f"  Expected: {'FAIL' if expected_fail else 'PASS'}")

        # Command to run PeTTa (need to use bash explicitly)
        cmd = [
            "bash",
            str(self.petta_runner_path),
            str(test_path),
            "--silent" # Suppress MORK init: done and other PeTTa internal prints
        ]

        start_time = time.time()
        try:
            # Run from PeTTa directory so run.sh can find src/main.pl
            petta_dir = self.petta_runner_path.parent
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=120, # Increased timeout for PeTTa tests
                cwd=petta_dir
            )
            output = result.stdout + result.stderr
            duration = time.time() - start_time

            # Check if DV error was produced
            has_dv_error = "Disjoint variable violation" in output
            actual_failed = has_dv_error

            return TestResult(
                name=test_name,
                expected_fail=expected_fail,
                actual_failed=actual_failed,
                output=output,
                duration=duration
            )

        except subprocess.TimeoutExpired:
            duration = time.time() - start_time
            return TestResult(
                name=test_name,
                expected_fail=expected_fail,
                actual_failed=False,  # Timeout = didn't produce error
                output="TIMEOUT after 120s",
                duration=duration
            )
        except Exception as e:
            duration = time.time() - start_time
            return TestResult(
                name=test_name,
                expected_fail=expected_fail,
                actual_failed=False,
                output=f"ERROR: {e}",
                duration=duration
            )

    def print_result(self, result: TestResult):
        """Print result for a single test"""
        if result.passed:
            status = f"{GREEN}✓ PASS{RESET}"
        else:
            status = f"{RED}✗ FAIL{RESET}"

        expected = "should-fail" if result.expected_fail else "should-pass"
        actual = "failed" if result.actual_failed else "passed"

        print(f"{status} {result.name:40s} ({expected:12s} | {actual:6s}) {result.duration:.2f}s")

        if not result.passed and self.verbose:
            print(f"  {YELLOW}Output snippet:{RESET}")
            lines = result.output.split('\n')
            # Show error lines or last few lines
            error_lines = [l for l in lines if 'Error' in l or 'TEST' in l]
            if error_lines:
                for line in error_lines[:5]:
                    print(f"    {line}")
            else:
                for line in lines[-5:]:
                    print(f"    {line}")

    def run_all(self) -> int:
        """Run all tests and return exit code"""
        tests = self.find_tests()

        if not tests:
            print(f"{RED}No tests found!{RESET}")
            return 1

        print(f"{BOLD}{'='*70}{RESET}")
        print(f"{BOLD}PeTTa mmverify-utils.metta Test Suite (DV tests){RESET}")
        print(f"{BOLD}{'='*70}{RESET}")
        print(f"Found {len(tests)} tests\n")

        # Run tests
        for test_path in tests:
            result = self.run_test(test_path)
            self.results.append(result)
            self.print_result(result)

        # Summary
        print(f"\n{BOLD}{'='*70}{RESET}")
        print(f"{BOLD}Summary{RESET}")
        print(f"{BOLD}{'='*70}{RESET}")

        passed = sum(1 for r in self.results if r.passed)
        failed = sum(1 for r in self.results if not r.passed)
        total = len(self.results)
        total_time = sum(r.duration for r in self.results)

        print(f"Total tests:    {total}")
        print(f"Passed:         {GREEN}{passed}{RESET}")
        print(f"Failed:         {RED}{failed}{RESET}")
        print(f"Total time:     {total_time:.2f}s")

        if failed > 0:
            print(f"\n{RED}Failed tests:{RESET}")
            for r in self.results:
                if not r.passed:
                    expected = "fail" if r.expected_fail else "pass"
                    actual = "failed" if r.actual_failed else "passed"
                    print(f"  {r.name}: expected {expected}, but {actual}")

        print(f"{BOLD}{'='*70}{RESET}")

        if failed == 0:
            print(f"{GREEN}{BOLD}✓ All tests passed!{RESET}")
            return 0
        else:
            print(f"{RED}{BOLD}✗ Some tests failed{RESET}")
            return 1

def main():
    parser = argparse.ArgumentParser(
        description="Test driver for mmverify-utils.metta (PeTTa)",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('-v', '--verbose', action='store_true',
                        help='Verbose output')
    parser.add_argument('-f', '--filter', type=str,
                        help='Filter tests by name pattern')

    args = parser.parse_args()

    runner = PeTTaTestRunner(verbose=args.verbose, filter_pattern=args.filter)
    exit_code = runner.run_all()
    sys.exit(exit_code)

if __name__ == '__main__':
    main()
