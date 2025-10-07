#!/usr/bin/env sh
# Wrapper for metamath.exe to work with automated testing
# Usage: mmverify_wrapper.sh path/to/file.mm

set -eu

if [ $# -lt 1 ]; then
  echo "Usage: $0 path/to/file.mm" >&2
  exit 2
fi

MM_FILE="$1"

# Build command script
CMD="READ \"${MM_FILE}\"
VERIFY PROOF *
EXIT
"

# Run metamath
OUT="$(printf "%s" "$CMD" | metamath 2>&1)"
printf "%s\n" "$OUT"

# Check for actual errors (not "No errors")
if echo "$OUT" | grep -q "^?Error"; then
  exit 1
fi

# Check for failed proofs
if echo "$OUT" | grep -qi "FAILED"; then
  exit 1
fi

# Check for explicit error count
if echo "$OUT" | grep -qE "[1-9][0-9]* errors? (were|was) found"; then
  exit 1
fi

exit 0
