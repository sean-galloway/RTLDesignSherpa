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

# update_fst_tracing

The `update_fst_tracing` script at `bin/update_fst_tracing.py` is an automated code modification tool that updates CocoTB test files to enable FST (Fast Signal Trace) waveform generation with Verilator. It intelligently detects indentation styles, preserves formatting, and adds the necessary Verilator configuration to generate FST waveform dumps for debugging.

## Overview

FST is the modern waveform format used by GTKWave and Verilator for simulation trace data. It provides better compression and faster loading than VCD format. This script automates the tedious process of updating test files to enable FST tracing, ensuring consistent configuration across all tests while respecting each file's unique formatting style.

## Features

### Smart Indentation Detection

- Automatically detects the indentation style used in each file (spaces vs. tabs)
- Preserves existing indentation patterns
- Determines indent width from file analysis
- Maintains code style consistency

### Selective Updating

- Skips files already configured for FST tracing
- Checks for existing compile_args, sim_args, and plusargs
- Only adds missing configuration elements
- Prevents duplicate entries

### Comprehensive Configuration

Adds complete FST tracing setup:
- **Compile Arguments**: `--trace-fst`, `--trace-structs`, `--trace-depth 99`
- **Simulation Arguments**: `--trace-fst`, `--trace-structs`, `--trace-depth 99`
- **Plus Arguments**: `+trace`
- **Environment Variables**: `TRACE_FILE`, `VERILATOR_TRACE`
- **Wave Generation**: Sets `waves=True` in run() call

### Format Preservation

- Maintains existing code structure
- Preserves comment formatting
- Respects line breaks and spacing
- Keeps array/dictionary alignment

## Usage

The script provides a command-line interface for batch processing test files:

```bash
python3 bin/update_fst_tracing.py <directory> [--pattern PATTERN] [--dry-run]
```

### Command-Line Options

- `directory` (required): Directory containing test files to update

- `--pattern PATTERN`: Filename pattern to match (default: `test_*.py`)
  - Supports glob patterns
  - Common patterns: `test_*.py`, `cocotb_*.py`, `*_test.py`

- `--dry-run`: Print what would be done without making changes
  - Useful for previewing modifications
  - Safe way to verify which files would be updated

## Examples

### Update All Tests in Directory

Process all test_*.py files in val/common:
```bash
python3 bin/update_fst_tracing.py val/common
```

### Dry Run Preview

Preview changes without modifying files:
```bash
python3 bin/update_fst_tracing.py val/common --dry-run
```

### Custom Pattern

Update files matching custom pattern:
```bash
python3 bin/update_fst_tracing.py val/amba --pattern "cocotb_*.py"
```

### Recursive Processing

Process all subdirectories (pattern is recursive by default):
```bash
python3 bin/update_fst_tracing.py val/
```
This finds all test_*.py files in val/ and all subdirectories.

### Specific Test Directory

Update specific test category:
```bash
python3 bin/update_fst_tracing.py projects/components/bridge/dv/tests
```

## Configuration Added

### Extra Environment Variables

Adds to `extra_env` dictionary:
```python
extra_env = {
    'TRACE_FILE': f"{sim_build}/dump.fst",
    'VERILATOR_TRACE': '1',  # Enable tracing
    # ... existing entries preserved
}
```

### Compile Arguments

Creates `compile_args` array:
```python
compile_args = [
    "--trace-fst",
    "--trace-structs",
    "--trace-depth", "99",
]
```

### Simulation Arguments

Creates `sim_args` array:
```python
sim_args = [
    "--trace-fst",  # Tell Verilator to use FST
    "--trace-structs",
    "--trace-depth", "99",
]
```

### Plus Arguments

Creates `plusargs` array:
```python
plusargs = [
    "+trace",
]
```

### Run Function Updates

Adds arguments to `run()` call:
```python
run(
    # ... existing arguments
    compile_args=compile_args,
    sim_args=sim_args,
    plusargs=plusargs,
    waves=True,
)
```

## Internal Functionality

### Indentation Detection (`detect_indentation`)

Analyzes file content to determine indentation style:
1. Finds all lines with indentation using regex `r'^(\s+)[^\s]'`
2. Collects all indent strings
3. Counts occurrence of each unique indent
4. Returns most common indent (defaults to 4 spaces if none found)

Example detection:
```python
# File with 4-space indentation
def test():
    compile_args = [    # 4 spaces detected
        "--trace-fst",  # 8 spaces (2x base)
    ]
```

### Item Indentation Detection (`get_item_indentation`)

Determines indentation for array/dictionary items:
1. Finds the collection start pattern (e.g., "extra_env = {")
2. Checks the next non-empty line
3. Extracts indentation from that line
4. Returns indent string (defaults to 4 spaces)

This ensures new items match existing item indentation.

### Smart Entry Detection

For each configuration section, the script:
1. Searches for existing section (e.g., `extra_env = {`)
2. Scans following lines for specific keys (e.g., `TRACE_FILE`)
3. Only adds entries if they don't already exist
4. Preserves all existing entries

### Syntax Preservation

The script handles complex Python syntax:

**Dictionary Inline Content:**
```python
extra_env = {'existing': 'value', 'other': 123}
# Becomes:
extra_env = {
    'TRACE_FILE': f"{sim_build}/dump.fst",
    'VERILATOR_TRACE': '1',  # Enable tracing
    'existing': 'value', 'other': 123}
```

**Multi-line Run Calls:**
```python
run(
    python_search=[tests_dir],
    verilog_sources=verilog_sources,
)
# Becomes:
run(
    python_search=[tests_dir],
    verilog_sources=verilog_sources,
    compile_args=compile_args,
    sim_args=sim_args,
    plusargs=plusargs,
    waves=True,
)
```

**Single-line Run Calls:**
```python
run(toplevel="module")
# Becomes:
run(
    toplevel="module",
    compile_args=compile_args,
    sim_args=sim_args,
    plusargs=plusargs,
    waves=True,
)
```

### Comma Handling

Intelligent comma insertion/preservation:
- Adds comma after previous parameter if missing
- Checks for `=` to distinguish parameters from values
- Handles trailing commas correctly
- Preserves Python syntax validity

### Wave Parameter Update

Updates existing `waves=False` to `waves=True`:
```python
# Pattern matching
waves_pattern = re.compile(r'waves\s*=\s*False')
# Replacement
waves_pattern.sub('waves=True', line)
```

Also adds `waves=True` if parameter doesn't exist.

## File Modification Logic

### Detection Phase

1. Read file content
2. Check for existing FST tracing configuration
3. If already configured, skip file
4. Detect indentation style

### Analysis Phase

1. Split content into lines
2. Find `extra_env` dictionary location
3. Find `run()` function call location
4. Determine insertion points for each section

### Modification Phase

1. **Extra_env Update:**
   - Locate opening brace
   - Insert new environment variables
   - Preserve existing entries
   - Maintain indentation

2. **Compile/Sim/Plus Args:**
   - Create new arrays before run() call
   - Use detected indentation
   - Add comment explaining trace depth

3. **Run() Update:**
   - Find all run() parameters
   - Check for existing args
   - Add missing parameters
   - Update waves parameter
   - Handle single/multi-line formats

### Output Phase

1. Reconstruct file from modified lines
2. Compare with original content
3. Only write if changes were made
4. Report update status

## Output Format

### Processing Messages

For each file processed:
```
Processing /path/to/test_file.py...
Updated /path/to/test_file.py for FST tracing
```

Or if already configured:
```
Processing /path/to/test_file.py...
File /path/to/test_file.py already updated for FST tracing, skipping...
```

Or if no changes needed:
```
Processing /path/to/test_file.py...
No changes needed for /path/to/test_file.py
```

### Summary

At completion:
```
Found 15 test files to process
Updated 12 test files
```

### Dry Run Mode

In dry run mode:
```
[DRY RUN] Would update /path/to/test_file.py
```

## Generated Waveform Files

After running updated tests, FST files are generated in:
```
sim_build/dump.fst
```

### Viewing Waveforms

Use GTKWave to view FST files:
```bash
gtkwave sim_build/dump.fst
```

### Trace Depth

The script sets `--trace-depth 99` to capture:
- All signal levels
- Struct internals
- Deep module hierarchies

This provides comprehensive debug visibility.

## Use Cases

### Enable Debugging for New Tests

When creating new tests, run once to enable waveforms:
```bash
python3 bin/update_fst_tracing.py projects/my_component/dv/tests
```

### Bulk Update Existing Tests

Upgrade all tests to use FST format:
```bash
python3 bin/update_fst_tracing.py val/ --pattern "test_*.py"
```

### Preview Changes Before Commit

Check what would be modified:
```bash
python3 bin/update_fst_tracing.py val/amba --dry-run
```

### Standardize Trace Configuration

Ensure all tests use consistent tracing setup:
```bash
# Run on entire test directory
python3 bin/update_fst_tracing.py val/
```

### Update After Framework Changes

When updating CocoTB or Verilator versions:
```bash
# Re-run to ensure compatibility
python3 bin/update_fst_tracing.py val/
```

## Troubleshooting

### Script Reports "Already Updated"

**Symptom:** Files skipped with "already updated" message

**Cause:** File contains `compile_args` and `--trace-fst`

**Solution:**
- This is correct behavior (prevents duplicate entries)
- To force re-update, manually remove FST configuration first
- Verify configuration is correct by checking file content

### Indentation Looks Wrong

**Symptom:** Generated code has inconsistent indentation

**Cause:** Mixed tabs/spaces or unusual indent width

**Solution:**
- Run through code formatter after script (e.g., black, autopep8)
- Check original file indentation consistency
- Script uses most common indent found

### Syntax Error After Update

**Symptom:** Python syntax error when running test

**Cause:** Rare edge case in comma handling

**Solution:**
- Check for missing/extra commas in run() call
- Verify array closing brackets align correctly
- Review generated code manually
- Report issue with file example

### No Waveform Generated

**Symptom:** Test runs but no dump.fst created

**Cause:** Verilator not configured for tracing or runtime issue

**Solutions:**
- Check Verilator supports FST (version 4.0+)
- Verify `waves=True` in run() call
- Check `VERILATOR_TRACE=1` in environment
- Look for Verilator errors in test output

### Partial Update

**Symptom:** Some sections updated but not others

**Cause:** Script couldn't find insertion points

**Solutions:**
- Check file has `run()` function call
- Verify `extra_env` dictionary exists
- Look for unusual formatting that breaks pattern matching
- Manually add missing sections using generated code as template

## Dependencies

### Standard Library Only

The script uses only Python standard library modules:
- `os` - File and path operations
- `re` - Regular expression pattern matching
- `argparse` - Command-line argument parsing
- `pathlib.Path` - Object-oriented path handling

No external dependencies required.

## Integration with CocoTB

This script integrates with the CocoTB test infrastructure:

### Before Update

Typical test file structure:
```python
@pytest.mark.parametrize(...)
def test_module(request, params):
    extra_env = {}
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        toplevel=dut_name,
        module=module,
    )
```

### After Update

Enhanced with FST tracing:
```python
@pytest.mark.parametrize(...)
def test_module(request, params):
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
    }

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    sim_args = [
        "--trace-fst",  # Tell Verilator to use FST
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = [
        "+trace",
    ]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        toplevel=dut_name,
        module=module,
        compile_args=compile_args,
        sim_args=sim_args,
        plusargs=plusargs,
        waves=True,
    )
```

### Result

After test execution:
- FST waveform file created in sim_build/dump.fst
- All signals traced with full hierarchy
- Struct internals visible
- Ready for GTKWave debugging

## Performance Considerations

### FST vs VCD

FST format advantages:
- **Size**: 5-10x smaller than VCD
- **Speed**: Faster writing during simulation
- **Loading**: Faster GTKWave startup
- **Compression**: Better compression algorithms

Example comparison:
- VCD: 500 MB
- FST: 50 MB (same signal set)

### Trace Depth Impact

`--trace-depth 99` enables comprehensive tracing:
- **Pro**: Complete visibility into all hierarchy levels
- **Con**: Larger waveform files, slower simulation
- **Recommendation**: Use for debugging, disable for regression

### Simulation Overhead

Tracing adds overhead:
- **Compile time**: +10-20% (struct tracing adds complexity)
- **Runtime**: +20-50% (signal dumping overhead)
- **Disk I/O**: Continuous writing during simulation

For large designs, consider:
- Selective signal tracing (reduce depth)
- Shorter simulation times
- Faster disk (SSD recommended)

---

[Back to Scripts Index](index.md)

---
