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

# Case Fix

## Overview

The `casefix.py` script is a utility tool for converting SystemVerilog `case` statements to `casez` statements throughout a codebase. This conversion is useful when you want to use don't-care conditions (`?`) in your case statements, which require the `casez` keyword in SystemVerilog.

**Location:** `bin/casefix.py`

**Purpose:** Automatically convert `case` to `casez` in SystemVerilog files while intelligently ignoring comments

**Key Features:**
- Recursive directory processing
- Preserves comments (both single-line `//` and multi-line `/* */`)
- Word-boundary matching to avoid replacing partial matches
- In-place file modification
- Progress reporting

## Usage

### Basic Command Line Usage

```bash
# Process all .sv files in a directory recursively
python3 bin/casefix.py
```

By default, the script processes all `.sv` files in the `./rtl` directory. To change the target directory, modify the `dir_path` variable in the script:

```python
# Example usage (at end of script)
dir_path = "./rtl"  # Change this to your target directory
process_sv_files(dir_path)
```

### As an Importable Module

You can also import and use the functions programmatically:

```python
from bin.casefix import convert_case_to_casez, process_sv_files

# Convert a single file
convert_case_to_casez("path/to/file.sv")

# Process all .sv files in a directory tree
process_sv_files("path/to/directory")
```

## How It Works

The script uses a two-pass approach to ensure comments are preserved:

1. **Comment Detection:** Tracks multi-line comment blocks (`/* ... */`) and single-line comments (`//`)
2. **Pattern Matching:** Uses regex word-boundary matching (`\bcase\b`) to avoid replacing partial matches like "uppercase" or "casement"
3. **Safe Replacement:** Only performs substitutions in active code, not in commented sections

### Processing Flow

```
For each .sv file:
  ├── Read all lines
  ├── For each line:
  │   ├── Check if inside multi-line comment (/* ... */)
  │   ├── Check if single-line comment (//)
  │   ├── If not a comment:
  │   │   └── Replace \bcase\b with casez
  │   └── Keep original if comment
  └── Write modified content back to file
```

## Examples

### Example 1: Simple Case Statement

**Before:**
```systemverilog
case (state)
    2'b00: next_state = IDLE;
    2'b01: next_state = ACTIVE;
    2'b1?: next_state = ERROR;  // Don't care in bit 0
    default: next_state = IDLE;
endcase
```

**After:**
```systemverilog
casez (state)
    2'b00: next_state = IDLE;
    2'b01: next_state = ACTIVE;
    2'b1?: next_state = ERROR;  // Don't care in bit 0
    default: next_state = IDLE;
endcase
```

### Example 2: Preserving Comments

**Before:**
```systemverilog
// This is a case statement example
case (opcode)
    /* Multi-line comment about case
       statements should be preserved */
    4'b0001: result = ADD;
    4'b001?: result = SUB;  // Handles both 0010 and 0011
endcase
```

**After:**
```systemverilog
// This is a case statement example
casez (opcode)
    /* Multi-line comment about case
       statements should be preserved */
    4'b0001: result = ADD;
    4'b001?: result = SUB;  // Handles both 0010 and 0011
endcase
```

## Technical Details

### Regular Expression Pattern

The script uses the pattern `r'\bcase\b'` which:
- `\b` = Word boundary (ensures "case" is a complete word)
- `case` = Literal string to match
- `\b` = Word boundary (prevents matching "casement", "uppercase", etc.)

### Comment Handling

**Single-line comments:**
```python
if stripped_line.startswith("//") or in_comment:
    modified_lines.append(line)
    continue
```

**Multi-line comments:**
```python
if "/*" in stripped_line:
    in_comment = True
if "*/" in stripped_line:
    in_comment = False
    modified_lines.append(line)
    continue
```

### File Processing

The script:
1. Reads entire file into memory
2. Processes line by line
3. Overwrites original file with modifications
4. Prints confirmation message

**Warning:** The script modifies files in-place. Ensure you have backups or version control before running.

## Limitations and Considerations

### Known Limitations

1. **In-place Modification:** Files are overwritten. Use version control or backups.
2. **Comment Edge Cases:** If `/*` and `*/` appear on the same line but in a string literal, they may be incorrectly detected.
3. **No Dry-Run Mode:** The script immediately modifies files without preview.
4. **Fixed Directory:** Requires code modification to change target directory.

### Best Practices

1. **Use Version Control:** Always run on version-controlled code
2. **Test First:** Try on a single file or small directory first
3. **Review Changes:** Use `git diff` to review modifications before committing
4. **Backup:** Keep backups of critical files

## Integration with RTL Design Flow

This tool fits into the RTL design flow at the code quality phase:

```
Design → Code Quality → Verification → Implementation
           ↑
      casefix.py
```

**Use Cases:**
- Converting legacy code to use `casez` for don't-care matching
- Standardizing case statement syntax across a project
- Preparing code for tools that require `casez` for don't-care conditions
- Refactoring existing FSM implementations

## Troubleshooting

### Issue: Script doesn't find files

**Cause:** Target directory doesn't exist or contains no `.sv` files

**Solution:** Verify the `dir_path` variable points to a valid directory with SystemVerilog files

### Issue: Comments are modified

**Cause:** Unusual comment formatting or nested comment structures

**Solution:** Review the affected files and manually correct. Consider reporting edge cases for script improvement.

### Issue: Partial words replaced

**Cause:** This should not occur due to word-boundary matching, but if it does:

**Solution:** Check the regex pattern and ensure `\b` boundaries are in place

## Related Tools

- **[Search and Replace Directory](search_and_replace_directory.md)** - More general pattern replacement tool
- **[Lint Wrapper](lint_wrap.md)** - Code quality and style checking
- **[Black](black.md)** - Python code formatting (different tool)

## Version History

- **Created:** 2025-10-18
- **Author:** sean galloway
- **License:** MIT

---

[Back to Scripts Index](index.md)

---
