# Metamath Verifier (mmverify) Project

## Quick Start

This directory contains mmverify.py - a Python tool for parsing Metamath databases and generating MeTTa verification code.

## Critical Rules

**NEVER GIT RESTORE WITHOUT PERMISSION** - Previous work may contain important fixes that get lost when using git restore. Always ask before reverting changes.

## Key Files

- **mmverify.py** - Main verifier that parses .mm files and generates MeTTa code
- **mmverify-utils_petta.metta** - PeTTa implementation of verification utilities
- **tests/mmverify-utils.metta** - HE MeTTa implementation of verification utilities
- **hol_normal.mm** - HOL database in normal (uncompressed) format
- **hol_petta.metta** - Generated PeTTa MeTTa verification file from hol_normal.mm

## Generating PeTTa MeTTa Files

Convert Metamath database to PeTTa MeTTa:

```bash
# First convert compressed .mm to normal form using metamath executable
cat > /tmp/metamath_convert.txt << 'EOF'
READ "input.mm"
WRITE SOURCE "output_normal.mm" /REWRAP
EXIT
EOF
cat /tmp/metamath_convert.txt | /path/to/metamath

# Then generate PeTTa MeTTa file
conda run -n hyperon python3 mmverify.py output_normal.mm \
    --petta \
    --petta-utils-import mmverify-utils_petta \
    --log-metta output_petta.metta \
    --only-metta-log
```

## Running PeTTa MeTTa Files

```bash
cd /home/zar/claude/hyperon/PeTTa
./run.sh ../metamath/mmverify/hol_petta.metta --silent
```

## Common Issues Fixed

### Frame Management
- `push-frame` and `pop-frame` must be defined in mmverify-utils_petta.metta
- `pop-frame` uses `($_  (println! ...))` NOT `(() (println! ...))` - the latter doesn't execute in PeTTa!

### Import Paths
- Use `--petta-utils-import` flag to specify relative import path for mmverify-utils_petta.metta
- Path is relative to where the generated file will be run from

## Testing

Run the test suite:

```bash
cd /home/zar/claude/hyperon/PeTTa
./run.sh ../metamath/mmverify/tests/test_pop_frame_petta.metta --silent
```
