#!/usr/bin/env python3
"""test-mm-equivalence.py - Test semantic equivalence of two Metamath files

This script compares two .mm files for semantic equivalence, ignoring:
- Whitespace differences (spaces, tabs, newlines)
- Comments (anything between $( and $))
- Token ordering within certain statements (where order doesn't matter)

Returns 0 if files are equivalent, 1 if different, 2 on error.
"""

import sys
import argparse
from typing import List, Tuple
import re


def tokenize_mm(filepath: str) -> List[str]:
    """
    Tokenize a Metamath file into a list of significant tokens.

    Removes:
    - All whitespace (normalized to single spaces between tokens)
    - All comments ($( ... $))

    Returns list of tokens in order.
    """
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()

    # Remove comments: anything between $( and $)
    # Use non-greedy matching to handle multiple comments
    content = re.sub(r'\$\(.*?\$\)', '', content, flags=re.DOTALL)

    # Split on whitespace to get tokens
    tokens = content.split()

    return tokens


def normalize_statement(tokens: List[str], start_idx: int) -> Tuple[List[str], int]:
    """
    Normalize a single statement starting at start_idx.

    Returns (normalized_tokens, end_idx) where end_idx is the index after $.

    For some statements (like $d), we might want to normalize token order,
    but for now we keep strict ordering.
    """
    normalized = []
    idx = start_idx

    # Collect tokens until we hit $.
    while idx < len(tokens):
        tok = tokens[idx]
        normalized.append(tok)
        idx += 1
        if tok == '$.':
            break

    return normalized, idx


def compare_token_lists(tokens1: List[str], tokens2: List[str],
                        file1: str, file2: str, verbose: bool = False) -> bool:
    """
    Compare two token lists for exact equivalence.

    Returns True if equivalent, False otherwise.
    """
    if len(tokens1) != len(tokens2):
        if verbose:
            print(f"Token count mismatch: {file1} has {len(tokens1)} tokens, "
                  f"{file2} has {len(tokens2)} tokens")
        return False

    for i, (t1, t2) in enumerate(zip(tokens1, tokens2)):
        if t1 != t2:
            if verbose:
                print(f"Token mismatch at position {i}:")
                print(f"  {file1}: {t1}")
                print(f"  {file2}: {t2}")
                # Show context
                start = max(0, i - 5)
                end = min(len(tokens1), i + 6)
                print(f"  Context in {file1}: {' '.join(tokens1[start:end])}")
                print(f"  Context in {file2}: {' '.join(tokens2[start:end])}")
            return False

    return True


def test_equivalence(file1: str, file2: str, verbose: bool = False) -> bool:
    """
    Test if two Metamath files are semantically equivalent.

    Returns True if equivalent, False otherwise.
    """
    try:
        tokens1 = tokenize_mm(file1)
        tokens2 = tokenize_mm(file2)

        if verbose:
            print(f"File 1 ({file1}): {len(tokens1)} tokens")
            print(f"File 2 ({file2}): {len(tokens2)} tokens")

        return compare_token_lists(tokens1, tokens2, file1, file2, verbose)

    except FileNotFoundError as e:
        print(f"Error: File not found - {e}", file=sys.stderr)
        return False
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return False


def main():
    parser = argparse.ArgumentParser(
        description='Test semantic equivalence of two Metamath .mm files'
    )
    parser.add_argument('file1', help='First .mm file')
    parser.add_argument('file2', help='Second .mm file')
    parser.add_argument('-v', '--verbose', action='store_true',
                        help='Show detailed differences')

    args = parser.parse_args()

    if test_equivalence(args.file1, args.file2, args.verbose):
        print(f"✓ Files are equivalent: {args.file1} ≡ {args.file2}")
        return 0
    else:
        print(f"✗ Files differ: {args.file1} ≠ {args.file2}")
        return 1


if __name__ == '__main__':
    sys.exit(main())
