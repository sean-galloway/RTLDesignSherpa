# RAPIDS RTL Lint Reports

This directory contains comprehensive lint reports for all RAPIDS RTL modules.

## Quick Start

```bash
# From repo root
./bin/lint_rapids.sh
```

This will:
1. **Delete all old reports** (prevents stale data confusion)
2. Run **three lint tools** on all 12 RAPIDS modules:
   - **Verilator** - RTL correctness, synthesizability
   - **Verible** - Style, naming conventions, best practices
   - **Yosys** - Synthesis-based linting, semantic errors
3. Generate individual reports for each module
4. Create a summary report

## Reports Organization

```
projects/components/rapids/reports/lint/
├── SUMMARY.txt                    # Quick overview
├── verilator/                     # Verilator reports
│   ├── scheduler.txt
│   ├── descriptor_engine.txt
│   └── ...
├── verible/                       # Style reports
│   ├── scheduler.txt
│   ├── descriptor_engine.txt
│   └── ...
└── yosys/                         # Synthesis reports
    ├── scheduler.txt
    ├── descriptor_engine.txt
    └── ...
```

## Understanding the Output

### Console Output
The script provides color-coded output:
- ✓ **Green** = Clean (no issues)
- ⚠ **Yellow** = Warnings (style issues, non-critical)
- ✗ **Red** = Errors (critical issues requiring fixes)

### Summary File
View the overall summary:
```bash
cat projects/components/rapids/reports/lint/SUMMARY.txt
```

Shows:
- Total modules linted
- Tools run and their results
- Module list
- Report locations

### Individual Reports

**Verilator** (`verilator/*.txt`):
- UNUSEDSIGNAL - Unused signals
- UNUSEDPARAM - Unused parameters
- TIMESCALEMOD - Timescale inconsistencies
- WIDTHEXPAND - Bit width mismatches
- BLKSEQ - Blocking assignments in sequential logic
- SYNCASYNCNET - Sync/async reset conflicts

**Verible** (`verible/*.txt`):
- Line length violations (>100 chars)
- Parameter naming conventions
- Trailing spaces
- Missing EOF newlines
- Explicit parameter types

**Yosys** (`yosys/*.txt`):
- Syntax errors
- Unsupported SystemVerilog constructs
- Semantic issues

## Common Workflows

### Quick Check - Are There Any Errors?
```bash
./bin/lint_rapids.sh
# Exit code 0 = no critical errors
# Exit code >0 = critical errors found
```

### View Specific Module Issues
```bash
# Verilator (functional issues)
cat projects/components/rapids/reports/lint/verilator/scheduler.txt

# Verible (style issues)
cat projects/components/rapids/reports/lint/verible/scheduler.txt

# Yosys (synthesis issues)
cat projects/components/rapids/reports/lint/yosys/simple_sram.txt
```

### Find All Modules with Errors
```bash
grep -l "Error" projects/components/rapids/reports/lint/verilator/*.txt
```

### Count Issues Per Module
```bash
for f in projects/components/rapids/reports/lint/verible/*.txt; do
    echo "$(basename $f): $(wc -l < $f) issues"
done | sort -t: -k2 -nr
```

## Why Old Reports Are Deleted

**Problem:** Stale reports can cause confusion
- If you rename or delete a module, old reports remain
- You might analyze reports for modules that no longer exist
- Makes it unclear which issues are current

**Solution:** Script deletes all reports before running
- Guarantees reports match current RTL
- `rm -rf projects/components/rapids/reports/lint`
- Fresh start every time

## Integration with CI/CD

The lint script returns non-zero exit code on critical errors:

```bash
# In CI/CD pipeline
./bin/lint_rapids.sh || exit 1

# Or more sophisticated
if ! ./bin/lint_rapids.sh; then
    echo "Lint failed - see reports"
    cat projects/components/rapids/reports/lint/SUMMARY.txt
    exit 1
fi
```

## Comparing Results Over Time

Since reports are regenerated each time, save snapshots:

```bash
# Before making changes
./bin/lint_rapids.sh
cp -r projects/components/rapids/reports/lint /tmp/lint_before

# Make your RTL changes
# ...

# After changes
./bin/lint_rapids.sh
cp -r projects/components/rapids/reports/lint /tmp/lint_after

# Compare
diff -r /tmp/lint_before/verilator /tmp/lint_after/verilator
```

## Known Limitations

### Verilator
- Warns about package import::* (expected behavior)
- Warns about unused package parameters (false positives)
- Some warnings in monitor_pkg.sv are from framework (ignore)

### Verible
- Parameter naming regex may be overly strict
- Some line length violations may be acceptable
- Not all suggested changes improve readability

### Yosys
- Doesn't support all SystemVerilog features
- `'{default:0}` initialization not supported (but valid SV)
- Include file handling has limitations

## Filtering Noise

To focus on critical issues:

```bash
# Verilator - only errors, skip warnings
grep "^%Error" projects/components/rapids/reports/lint/verilator/*.txt

# Verible - only line length violations (easiest to fix)
grep "line-length" projects/components/rapids/reports/lint/verible/*.txt

# Yosys - real syntax errors (skip include warnings)
grep "ERROR:" projects/components/rapids/reports/lint/yosys/*.txt | grep -v "Can't open include"
```

## Current Status

**Last run:** Check SUMMARY.txt for timestamp
**Modules:** 12 (9 rapids_fub + 3 rapids_macro)
**Tools:** Verilator ✓, Verible ✓, Yosys ✓

---

**Generated by:** bin/lint_rapids.sh
**Documentation:** bin/lint_rapids.sh (see header comments)
