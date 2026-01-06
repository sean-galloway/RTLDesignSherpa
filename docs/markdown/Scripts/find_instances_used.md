<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

**[← Back to Scripts Index](index.md)**

# Find Instances Used

## Overview

The `find_instances_used.py` script is a dependency analysis tool that scans through Makefiles to identify which RTL files (`.sv` files) are referenced in test builds. This helps you understand module usage patterns, identify unused modules, and track dependencies across the design hierarchy.

**Location:** `bin/find_instances_used.py`

**Purpose:** Analyze module instantiation dependencies by parsing Makefile `VERILOG_SOURCES` variables

**Key Features:**
- Recursive Makefile scanning
- Verilog file dependency tracking
- CSV output for analysis
- Module usage mapping
- Test-to-module relationship tracking

## Usage

### Command Line Arguments

```bash
python3 bin/find_instances_used.py [options]
```

### Required Arguments

| Argument | Short | Description |
|----------|-------|-------------|
| `--path` | `-p` | Path to start searching for Makefiles |

### Optional Arguments

| Argument | Short | Description |
|----------|-------|-------------|
| `--output` | `-o` | Output CSV file (default: `output.csv`) |
| `--verilog_path` | `-vp` | Path to list all .sv files to track |
| `--used_path` | `-u` | Output CSV file for used paths mapping |

## Examples

### Example 1: Basic Usage

Find all Verilog file usage in test Makefiles:

```bash
python3 bin/find_instances_used.py \
    --path val/common_level0 \
    --verilog_path rtl/common \
    --used_path common_usage.csv
```

This will:
1. Search for all `.sv` files in `rtl/common`
2. Scan all Makefiles in `val/common_level0` and subdirectories
3. Generate `common_usage.csv` showing which tests use which modules

### Example 2: Analysis of Specific Subsystem

```bash
python3 bin/find_instances_used.py \
    --path val/amba \
    --verilog_path rtl/amba \
    --used_path amba_module_usage.csv
```

### Example 3: Multi-Level Analysis

```bash
# Analyze both common and AMBA usage
python3 bin/find_instances_used.py \
    --path val \
    --verilog_path rtl \
    --used_path complete_usage.csv
```

## Output Format

### CSV Structure

The output CSV file contains:

```csv
module_name.sv,test1/,test2/,test3/
counter_bin.sv,test_counter/,test_fsm/,test_processor/
arbiter_rr.sv,test_arbiter/
fifo_sync.sv,test_fifo_sync/,test_buffering/
```

**Format:**
- **Column 1:** Verilog source file basename (e.g., `counter_bin.sv`)
- **Column 2+:** Comma-separated list of test directories that include this file in their `VERILOG_SOURCES`

### Example Output Analysis

```csv
counter_bin.sv,test_counter/,test_timer/,test_pwm/
arbiter_round_robin.sv,test_arbiter/,test_bus_controller/
fifo_async.sv,test_fifo_async/
data_width_converter.sv,
```

**Interpretation:**
- `counter_bin.sv` is used by 3 tests
- `arbiter_round_robin.sv` is used by 2 tests
- `fifo_async.sv` is used by 1 test
- `data_width_converter.sv` is not used by any test (empty usage list)

## How It Works

### Processing Flow

```
1. List all .sv files in verilog_path
   ↓
2. Initialize results dictionary
   ↓
3. Walk through path directory tree
   ↓
4. For each Makefile found:
   ├── Parse VERILOG_SOURCES variable
   ├── Extract file references
   ├── Match against tracked .sv files
   └── Record test directory path
   ↓
5. Generate CSV output
```

### Makefile Parsing

The script looks for this pattern in Makefiles:

```makefile
VERILOG_SOURCES = \
    $(REPO_ROOT)/rtl/common/counter_bin.sv \
    $(REPO_ROOT)/rtl/common/arbiter_rr.sv \
    $(REPO_ROOT)/rtl/amba/axi4_monitor.sv
```

**Parsing Rules:**
1. Finds `VERILOG_SOURCES = ...` declarations
2. Handles line continuations (`\`)
3. Strips `$(REPO_ROOT)/rtl/common/` prefix
4. Extracts basename of each file
5. Maps to test directory containing the Makefile

### Regular Expression Pattern

```python
pattern = r"VERILOG_SOURCES\s*=\s*((?:.*\\\n?)+)"
```

This matches:
- `VERILOG_SOURCES` keyword
- Optional whitespace
- `=` assignment
- Multi-line values (with `\` continuation)

## Use Cases

### 1. Identify Unused Modules

Find RTL modules that have no associated tests:

```bash
python3 bin/find_instances_used.py \
    --path val/common_level0 \
    --verilog_path rtl/common \
    --used_path usage.csv

# Check for empty usage lists in usage.csv
grep "^[^,]*,$" usage.csv
```

### 2. Refactoring Impact Analysis

Before modifying a module, see which tests will be affected:

```bash
# Generate usage report
python3 bin/find_instances_used.py \
    --path val \
    --verilog_path rtl \
    --used_path all_usage.csv

# Search for specific module
grep "counter_bin.sv" all_usage.csv
```

### 3. Test Coverage Analysis

Understand test distribution across modules:

```python
import csv

usage = {}
with open('usage.csv', 'r') as f:
    reader = csv.reader(f)
    for row in reader:
        module = row[0]
        tests = [t for t in row[1:] if t]
        usage[module] = len(tests)

# Sort by usage count
for module, count in sorted(usage.items(), key=lambda x: x[1]):
    print(f"{module}: {count} tests")
```

### 4. Dependency Tracking

Track which subsystems depend on common infrastructure:

```bash
# Find all tests using common modules
python3 bin/find_instances_used.py \
    --path val \
    --verilog_path rtl/common \
    --used_path common_dependencies.csv
```

## Technical Details

### File Path Handling

The script performs path normalization:

```python
line = line.strip()
    .replace('\\', '')                        # Remove line continuations
    .replace('$(REPO_ROOT)/rtl/common/', '')  # Remove prefix
    .strip()                                  # Clean whitespace
```

**Note:** The current implementation has a hardcoded prefix replacement for `$(REPO_ROOT)/val/common_level0/`. This may need adjustment for other subsystems.

### Data Structure

Internal representation:

```python
results = {
    'counter_bin.sv': ['test_counter/', 'test_timer/'],
    'arbiter_rr.sv': ['test_arbiter/'],
    'fifo_sync.sv': [],  # No tests found
}
```

### CSV Generation

```python
with open(args.used_path, 'w') as csv_file:
    for key, paths in results.items():
        csv_file.write(f"{key},{','.join(paths)}\n")
```

## Limitations and Considerations

### Known Limitations

1. **Hardcoded Paths:** The script has hardcoded path replacements that may need modification for different subsystems
2. **VERILOG_SOURCES Only:** Only parses `VERILOG_SOURCES` variable, not other potential file list variables
3. **No Include Files:** Doesn't track `.svh` or other include files
4. **Single Format:** Assumes specific Makefile format and variable naming
5. **No Dependency Depth:** Only tracks direct file inclusion, not transitive dependencies through module instantiation

### Best Practices

1. **Consistent Makefiles:** Ensure all test Makefiles use `VERILOG_SOURCES` variable
2. **Path Conventions:** Use consistent path prefixes (e.g., `$(REPO_ROOT)/rtl/...`)
3. **Regular Analysis:** Run periodically to identify unused modules
4. **Combine with Coverage:** Use alongside code coverage tools for complete picture

## Integration with RTL Design Flow

This tool fits into the analysis phase:

```
Design → Analysis → Verification → Implementation
           ↑
    find_instances_used.py
```

**Workflow Integration:**
1. **Before Refactoring:** Check module usage before making changes
2. **Code Review:** Verify new tests include necessary modules
3. **Cleanup:** Identify and remove unused modules
4. **Documentation:** Generate module usage documentation

## Troubleshooting

### Issue: Empty results

**Cause:** No Makefiles found or incorrect path

**Solution:** Verify `--path` argument points to directory containing Makefiles

### Issue: Missing modules in output

**Cause:** Makefile format doesn't match expected pattern

**Solution:** Check that Makefiles use `VERILOG_SOURCES = \` format with line continuations

### Issue: Wrong path prefixes in results

**Cause:** Hardcoded path replacement doesn't match your structure

**Solution:** Modify the `parse_makefile()` function to use appropriate path replacement

### Issue: Symbolic links not followed

**Cause:** `os.walk()` doesn't follow symlinks by default

**Solution:** Modify `os.walk()` call to `os.walk(path, followlinks=True)` if needed

## Related Tools

- **[Structure Test Script](struct_test_script.md)** - Automated structural testing
- **[Search and Replace Directory](search_and_replace_directory.md)** - Batch file processing
- **[PyTree](pytree.md)** - Directory visualization

## Version History

- **Created:** 2025-10-18
- **Author:** sean galloway
- **License:** MIT

---

[Back to Scripts Index](index.md)

---
