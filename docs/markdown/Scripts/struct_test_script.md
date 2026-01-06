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

# struct_test_script

The `struct_test_script` at `bin/struct_test_script.py` is a comprehensive testing utility for the CocoTB framework's struct-related functionality. It systematically tests all struct parsing, field extraction, and code generation functions to ensure they work correctly before using them in actual testbenches.

## Overview

This script provides automated testing and validation of the struct utilities infrastructure, which is critical for generating Python helper code from SystemVerilog struct definitions. It tests both direct extraction functions and auto-discovery capabilities, making it an essential tool for debugging struct-related issues in the verification framework.

## Features

### Comprehensive Function Testing

Tests all major struct utility functions:
- `validate_struct_setup()` - Verifies struct file format and availability
- `list_available_structs()` - Discovers all struct definitions in a file
- `get_struct_info()` - Extracts detailed struct metadata
- `extract_struct_for_test()` - Direct extraction with path specification
- `extract_struct_for_test_simple()` - Auto-find extraction from repo
- `setup_struct_environment()` - Environment variable generation

### File and Path Validation

- Checks file existence and accessibility
- Validates absolute path resolution
- Inspects file content for struct markers
- Verifies struct name presence in file

### Generated File Verification

- Checks all generated output files
- Validates Python helper imports
- Verifies function availability (pack_struct, unpack_struct)
- Confirms STRUCT_FIELDS dictionary generation

### Detailed Diagnostic Output

- Formatted section headers for clarity
- Success/failure indicators with checkmarks
- Comprehensive error messages
- Preserved temp directory for manual inspection

## Usage

The script requires two command-line arguments:

```bash
python3 bin/struct_test_script.py <struct_file_path> <struct_name>
```

### Arguments

- `struct_file_path`: Path to the SystemVerilog file containing struct definitions
- `struct_name`: Name of the specific struct to test

### Examples

#### Test with Valid Struct

Test the axi_narrow struct from the buffer_field_struct.sv file:
```bash
python3 bin/struct_test_script.py rtl/amba/testcode/include/buffer_field_struct.sv axi_narrow
```

#### Test with Invalid Path

Test error handling for non-existent file:
```bash
python3 bin/struct_test_script.py /bad/path/file.sv axi_narrow
```

Expected output: File existence check fails, but script continues to test error handling

#### Test with Invalid Struct Name

Test error handling for non-existent struct:
```bash
python3 bin/struct_test_script.py rtl/amba/testcode/include/buffer_field_struct.sv bad_struct
```

Expected output: Struct name check fails, error messages from extraction functions

## Test Sequence

The script performs 9 sequential test sections:

### 1. File Existence Check

Validates the struct file:
- Converts path to absolute
- Checks file existence
- Reports file size
- Inspects content for 'StructStart' marker
- Verifies struct name presence

Example output:
```
------------------------------------------------------------
 1. File Existence Check
------------------------------------------------------------
Absolute path: /path/to/rtl/amba/testcode/include/buffer_field_struct.sv
File exists: True
File size: 15234 bytes
Content length: 15234 characters
Contains 'StructStart': True
Contains 'axi_narrow': True
```

### 2. Import CocoTB Utilities

Attempts to import all struct utility functions:
- extract_struct_for_test
- extract_struct_for_test_simple
- setup_struct_environment
- validate_struct_setup
- list_available_structs
- get_struct_info

Success indicator: "✓ Successfully imported all struct utilities"

### 3. Testing validate_struct_setup()

Validates the struct file format and reports:
- Success status (True/False)
- Validation message
- List of available structs found in file

Example output:
```
Success: True
Message: File contains valid struct definitions
Available structs: ['axi_narrow', 'axi_wide', 'apb_transaction']
```

### 4. Testing list_available_structs()

Lists all struct definitions in the file:
- Returns array of struct names
- Checks if target struct is in the list

Example output:
```
Available structs: ['axi_narrow', 'axi_wide', 'apb_transaction']
Target struct 'axi_narrow' in list: True
```

### 5. Testing get_struct_info()

Extracts detailed metadata for the specified struct:
- Typedef name
- Total bit width
- Field information (names and widths)
- Validation status

Example output:
```
✓ Found struct info for 'axi_narrow':
  Typedef name: axi_narrow_t
  Bit width: 128
  Fields (8):
    addr: 32 bits
    len: 8 bits
    size: 3 bits
    burst: 2 bits
    ...
  Validation: ✓ Struct definition is valid
```

### 6. Testing extract_struct_for_test() (direct)

Performs direct extraction with explicit path:
- Extracts struct definition
- Generates Python helpers
- Creates SystemVerilog include files
- Reports all generated files

Example output:
```
✓ Direct extraction successful!
  Success: True
  Struct name: axi_narrow
  Typedef name: axi_narrow_t
  Bit width: 128
  Field count: 8
  Generated files:
    python_helpers: /tmp/tmpXYZ/axi_narrow_helpers.py (exists: True)
    sv_include: /tmp/tmpXYZ/axi_narrow.svh (exists: True)
    json_definition: /tmp/tmpXYZ/axi_narrow.json (exists: True)
```

### 7. Testing setup_struct_environment()

Generates environment variables from struct metadata:
- Creates variables for each field
- Generates bit position and width constants
- Returns dictionary of all environment variables

Example output:
```
✓ Generated 24 environment variables:
  AXI_NARROW_ADDR_WIDTH = '32'
  AXI_NARROW_ADDR_LSB = '0'
  AXI_NARROW_ADDR_MSB = '31'
  AXI_NARROW_LEN_WIDTH = '8'
  AXI_NARROW_LEN_LSB = '32'
  AXI_NARROW_LEN_MSB = '39'
  ...
```

### 8. Testing extract_struct_for_test_simple() (auto-find)

Tests auto-discovery extraction:
- Uses repo root to search for struct file
- Automatically finds file containing struct definition
- Extracts and reports basic info

Note: This test may fail if the struct file is not in standard search locations. This is expected behavior and documented in the output.

Example output:
```
✓ Auto-find extraction successful!
  Found and extracted: axi_narrow
  Typedef name: axi_narrow_t
  Bit width: 128
```

### 9. Checking Generated Files

Validates all generated files and attempts to import Python helpers:
- Checks file existence for each generated file
- Imports Python helpers module
- Verifies STRUCT_FIELDS dictionary
- Confirms pack_struct and unpack_struct functions

Example output:
```
✓ python_helpers: /tmp/tmpXYZ/axi_narrow_helpers.py
  ✓ Successfully imported generated Python helpers
  ✓ STRUCT_FIELDS available: ['addr', 'len', 'size', 'burst', ...]
  ✓ pack_struct function available
  ✓ unpack_struct function available
✓ sv_include: /tmp/tmpXYZ/axi_narrow.svh
✓ json_definition: /tmp/tmpXYZ/axi_narrow.json
```

## Output Format

### Section Headers

Major sections use double-line borders:
```
================================================================================
 Testing Struct Utilities
================================================================================
```

Subsections use single-line borders:
```
------------------------------------------------------------
 1. File Existence Check
------------------------------------------------------------
```

### Status Indicators

- `✓` - Success/available/found
- `✗` - Failure/unavailable/not found
- `Warning:` - Non-critical issue

### Summary

The script concludes with:
```
================================================================================
 Test Summary
================================================================================
Temp directory (preserved for inspection): /tmp/tmpXYZ
Review the output above to see which functions work and which don't.
```

## Generated Files

The script creates several output files in a temporary directory:

### Python Helpers (struct_name_helpers.py)

Contains:
- `STRUCT_FIELDS` dictionary with field metadata
- `pack_struct(fields_dict)` function for encoding
- `unpack_struct(packed_value)` function for decoding
- Bit manipulation utilities

### SystemVerilog Include (struct_name.svh)

Contains:
- Typedef definition
- Macro definitions for field extraction
- Width and position constants

### JSON Definition (struct_name.json)

Contains:
- Complete struct metadata
- Field definitions with positions and widths
- Validation information

## Internal Functionality

### Test Orchestration (`test_struct_utilities`)

Main testing function that:
1. Prints formatted header with test configuration
2. Creates temporary directory for outputs
3. Executes 9 sequential test sections
4. Preserves temp directory for manual inspection
5. Returns success/failure status

### Formatted Output (`print_header`, `print_section`)

Utility functions for consistent output formatting:
- `print_header()` - 80-character double-line borders
- `print_section()` - 60-character single-line borders

### Import Validation

Uses try/except to import utilities:
- Catches ImportError exceptions
- Reports specific missing modules
- Allows testing to continue after import failures

### File Import Testing

For generated Python helpers:
- Uses `importlib.util` for dynamic import
- Loads module from file path
- Checks for required attributes and functions
- Reports availability with checkmarks

## Error Handling

The script handles various error conditions gracefully:

### File Not Found

Continues testing to validate error handling:
```
File exists: False
File size: <error>
Content length: <error>
Contains 'StructStart': <error>
```

### Import Failures

Reports specific import errors but continues:
```
✗ Failed to import utilities: No module named 'CocoTBFramework'
```

### Struct Not Found

Reports validation failures:
```
✗ No struct info found for 'bad_struct'
✗ validate_struct_setup failed: Struct 'bad_struct' not found in file
```

### Auto-Find Failures

Acknowledges expected failures:
```
✗ extract_struct_for_test_simple failed: Could not locate struct file
   This is expected if the file isn't in standard search locations
```

## Use Cases

### Pre-Test Validation

Before writing testbench code using struct utilities:
```bash
python3 bin/struct_test_script.py rtl/amba/testcode/include/buffer_field_struct.sv axi_narrow
```

Confirms all utilities work correctly.

### Debug Struct Parsing

When struct extraction fails in testbench:
```bash
python3 bin/struct_test_script.py path/to/struct.sv problematic_struct
```

Identifies which specific function is failing.

### Verify New Struct Definitions

After adding new struct to file:
```bash
python3 bin/struct_test_script.py rtl/custom/my_structs.sv new_struct
```

Ensures struct is properly formatted and parseable.

### Compare Different Struct Files

Test multiple struct files to compare functionality:
```bash
python3 bin/struct_test_script.py file1.sv struct_a
python3 bin/struct_test_script.py file2.sv struct_b
```

### Integration Testing

Verify struct utilities work in specific environment:
```bash
cd /path/to/test/environment
python3 ../../bin/struct_test_script.py rtl/include/structs.sv my_struct
```

## Dependencies

### Required

- **Python 3.6+**: For pathlib and type hints
- **CocoTBFramework**: Must be in Python path (../../bin)
- **Struct utilities module**: CocoTBFramework.tbclasses.misc.utilities

### Standard Library

- `sys` - System path and arguments
- `os` - File and path operations
- `tempfile` - Temporary directory creation
- `pathlib.Path` - Object-oriented path handling
- `importlib.util` - Dynamic module import

## Troubleshooting

### Import Errors

**Symptom:** "Failed to import utilities"

**Solutions:**
- Check Python path includes bin/ directory
- Verify CocoTBFramework exists in bin/
- Run from repository root directory
- Check for circular import issues

### File Not Found

**Symptom:** "File exists: False"

**Solutions:**
- Use absolute path or path relative to current directory
- Verify file permissions (readable)
- Check for typos in file path

### Struct Not Found

**Symptom:** "No struct info found for 'struct_name'"

**Solutions:**
- Check struct name spelling (case-sensitive)
- Verify struct has StructStart/StructEnd markers
- Inspect file content for struct definition format
- Review struct definition syntax

### Auto-Find Fails

**Symptom:** "extract_struct_for_test_simple failed"

**Solutions:**
- Use direct path with extract_struct_for_test()
- Verify file is in standard search locations
- Check repo_root parameter is correct
- This is expected for custom struct locations

### Generated Files Not Found

**Symptom:** "python_helpers: /tmp/... (exists: False)"

**Solutions:**
- Check temp directory permissions
- Verify struct extraction succeeded
- Look for error messages in earlier test sections
- Check disk space availability

## Integration with CocoTB Framework

This test script validates the infrastructure used by CocoTB testbenches:

1. **Struct Definition Files**: SystemVerilog files with StructStart/StructEnd markers
2. **Extraction Functions**: Parse struct definitions into metadata
3. **Code Generators**: Create Python helpers and SV includes
4. **Testbench Integration**: Generated code used in testbench setup

Example testbench usage after validation:
```python
# In testbench code (after running struct_test_script.py to verify)
from CocoTBFramework.tbclasses.misc.utilities import extract_struct_for_test

struct_info = extract_struct_for_test(
    struct_file='rtl/amba/testcode/include/buffer_field_struct.sv',
    struct_name='axi_narrow',
    output_dir='sim_build'
)

# Import generated helpers
sys.path.insert(0, 'sim_build')
from axi_narrow_helpers import pack_struct, unpack_struct, STRUCT_FIELDS
```

## Temp Directory Preservation

The script preserves the temporary directory for manual inspection:
- All generated files remain available after script completion
- Directory path printed in test summary
- Useful for debugging generation issues
- Can be manually deleted when no longer needed

Example preservation message:
```
================================================================================
 Test Summary
================================================================================
Temp directory (preserved for inspection): /tmp/tmp_abc123xyz
Review the output above to see which functions work and which don't.
```

---

[Back to Scripts Index](index.md)

---
