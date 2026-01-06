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

# Search and Replace Directory

## Overview

The `search_and_replace_directory.py` script is a powerful batch text processing tool that recursively searches through a directory tree and performs regex-based search and replace operations on file contents. It supports file extension filtering and automatically skips symbolic links for safety.

**Location:** `bin/search_and_replace_directory.py`

**Purpose:** Recursively search and replace text patterns across multiple files using regular expressions

**Key Features:**
- Recursive directory traversal
- Regular expression pattern matching
- File extension filtering
- Symbolic link protection
- UTF-8 encoding with error handling
- In-place file modification
- Progress reporting

## Usage

### Command Line Arguments

```bash
python3 bin/search_and_replace_directory.py <directory> <pattern> <replacement> [options]
```

### Required Arguments

| Argument | Description |
|----------|-------------|
| `directory` | Root directory to search for files |
| `search_pattern` | Regular expression pattern to search for |
| `replace_text` | Text to replace matched patterns with |

### Optional Arguments

| Argument | Description |
|----------|-------------|
| `--file-extensions` | List of file extensions to process (e.g., `.txt .py .sv`) |

## Examples

### Example 1: Simple Text Replacement

Replace all occurrences of "old_name" with "new_name" in all files:

```bash
python3 bin/search_and_replace_directory.py \
    rtl/common \
    "old_name" \
    "new_name"
```

### Example 2: Regex Pattern Replacement

Replace signal names using regex pattern:

```bash
python3 bin/search_and_replace_directory.py \
    rtl/amba \
    "i_(\w+)_valid" \
    "i_\1_vld"
```

This changes `i_data_valid` to `i_data_vld`, `i_addr_valid` to `i_addr_vld`, etc.

### Example 3: File Extension Filtering

Replace only in SystemVerilog files:

```bash
python3 bin/search_and_replace_directory.py \
    rtl \
    "reg\s+(\w+);" \
    "logic \1;" \
    --file-extensions .sv .svh
```

### Example 4: Python Import Refactoring

Update import statements across Python test files:

```bash
python3 bin/search_and_replace_directory.py \
    val/amba \
    "from tbclasses\.(\w+) import" \
    "from CocoTBFramework.tbclasses.\1 import" \
    --file-extensions .py
```

### Example 5: Multi-line Pattern (Advanced)

Replace parameter declarations:

```bash
python3 bin/search_and_replace_directory.py \
    rtl/common \
    "parameter\s+int\s+(\w+)\s*=" \
    "parameter int unsigned \1 =" \
    --file-extensions .sv
```

## How It Works

### Processing Flow

```
1. Validate directory exists
   ↓
2. Walk directory tree recursively
   ↓
3. For each file found:
   ├── Check if symbolic link → Skip
   ├── Check file extension filter → Skip if not matching
   ├── Read file contents (UTF-8 with error handling)
   ├── Apply regex substitution
   ├── Compare original vs modified content
   └── If changed → Write back to file
   ↓
4. Print summary of updated files
```

### Regex Substitution

The script uses Python's `re.sub()` function:

```python
updated_content = re.sub(search_pattern, replace_text, content)
```

This supports:
- Basic patterns: `"counter"` → `"counter_new"`
- Capture groups: `r"(\w+)_old"` → `r"\1_new"`
- Quantifiers: `r"signal\s+"` matches "signal" followed by any whitespace
- Character classes: `r"[0-9]+"` matches numbers

### File Handling

**Reading:**
```python
with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
    content = f.read()
```

**Writing:**
```python
if content != updated_content:
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(updated_content)
    print(f"Updated: {filepath}")
```

**Symbolic Link Protection:**
```python
if os.path.islink(filepath):
    print(f"Skipping symbolic link: {filepath}")
    continue
```

## Regular Expression Patterns

### Common Patterns

**Simple String Matching:**
```bash
# Replace exact string
python3 bin/search_and_replace_directory.py dir "old_text" "new_text"
```

**Word Boundaries:**
```bash
# Replace whole words only (avoid partial matches)
python3 bin/search_and_replace_directory.py dir "\\bwidth\\b" "data_width"
```

**Capture Groups:**
```bash
# Reuse matched text
python3 bin/search_and_replace_directory.py dir "signal_(\w+)" "wire_\1"
# Matches: signal_data → wire_data, signal_addr → wire_addr
```

**Optional Whitespace:**
```bash
# Handle varying whitespace
python3 bin/search_and_replace_directory.py dir "parameter\s+(\w+)" "localparam \1"
```

**Multiple Alternatives:**
```bash
# Match multiple patterns
python3 bin/search_and_replace_directory.py dir "(ready|valid)" "\1_signal"
```

### SystemVerilog-Specific Patterns

**Port Direction Change:**
```bash
python3 bin/search_and_replace_directory.py \
    rtl \
    "input\s+logic" \
    "input wire logic" \
    --file-extensions .sv
```

**Signal Naming Convention:**
```bash
# Add prefix to signals
python3 bin/search_and_replace_directory.py \
    rtl/common \
    "(\s+)(\w+_valid)" \
    "\1i_\2" \
    --file-extensions .sv
```

**Module Name Update:**
```bash
python3 bin/search_and_replace_directory.py \
    rtl/amba \
    "module\s+axi_(\w+)" \
    "module axi4_\1" \
    --file-extensions .sv
```

## Use Cases

### 1. Module Renaming

Rename module across entire subsystem:

```bash
python3 bin/search_and_replace_directory.py \
    rtl/common \
    "arbiter_rr" \
    "arbiter_round_robin" \
    --file-extensions .sv .svh
```

### 2. Signal Prefix Standardization

Add consistent prefixes to signals:

```bash
# Add i_ prefix to inputs
python3 bin/search_and_replace_directory.py \
    rtl/amba \
    "input\s+logic\s+(\w+)" \
    "input logic i_\1" \
    --file-extensions .sv

# Add o_ prefix to outputs
python3 bin/search_and_replace_directory.py \
    rtl/amba \
    "output\s+logic\s+(\w+)" \
    "output logic o_\1" \
    --file-extensions .sv
```

### 3. Copyright Header Updates

Update copyright year across all files:

```bash
python3 bin/search_and_replace_directory.py \
    . \
    "Copyright \(c\) 2024" \
    "Copyright (c) 2025" \
    --file-extensions .sv .py .md
```

### 4. Import Path Refactoring

Update Python import paths after reorganization:

```bash
python3 bin/search_and_replace_directory.py \
    val \
    "from tbclasses import" \
    "from CocoTBFramework.tbclasses import" \
    --file-extensions .py
```

### 5. Parameter Name Changes

Standardize parameter naming:

```bash
python3 bin/search_and_replace_directory.py \
    rtl \
    "parameter\s+WIDTH\s*=" \
    "parameter DATA_WIDTH =" \
    --file-extensions .sv
```

### 6. Comment Style Updates

Standardize comment formatting:

```bash
python3 bin/search_and_replace_directory.py \
    rtl/common \
    "//\s*TODO:" \
    "// TODO:" \
    --file-extensions .sv
```

## Advanced Usage

### Batch Operations

Execute multiple replacements sequentially:

```bash
#!/bin/bash
# Script: batch_rename.sh

SCRIPT="python3 bin/search_and_replace_directory.py"
DIR="rtl/amba"
EXT="--file-extensions .sv"

$SCRIPT $DIR "axi_monitor" "axi4_monitor" $EXT
$SCRIPT $DIR "apb_monitor" "apb3_monitor" $EXT
$SCRIPT $DIR "axis_monitor" "axis4_monitor" $EXT

echo "Batch rename complete"
```

### Dry Run with grep

Preview changes before applying:

```bash
# Check what will be replaced
grep -r "old_pattern" rtl/common --include="*.sv"

# Apply replacement
python3 bin/search_and_replace_directory.py \
    rtl/common "old_pattern" "new_pattern" --file-extensions .sv

# Verify changes
grep -r "new_pattern" rtl/common --include="*.sv"
```

### Backup Before Modification

Create backup before making changes:

```bash
# Create timestamped backup
tar -czf rtl_backup_$(date +%Y%m%d_%H%M%S).tar.gz rtl/

# Apply changes
python3 bin/search_and_replace_directory.py rtl "old" "new"

# If needed, restore from backup
# tar -xzf rtl_backup_YYYYMMDD_HHMMSS.tar.gz
```

### Integration with Version Control

Use with git to track changes:

```bash
# Create feature branch
git checkout -b refactor/rename_modules

# Apply replacement
python3 bin/search_and_replace_directory.py rtl "old_name" "new_name"

# Review changes
git diff

# Commit if satisfied
git add -A
git commit -m "Refactor: Rename old_name to new_name"
```

## Safety Considerations

### Backup Strategy

**Always backup before running:**

```bash
# Git repository (recommended)
git status  # Ensure clean working directory
git checkout -b backup/before_replacement

# Or create archive
tar -czf backup_$(date +%Y%m%d).tar.gz rtl/ val/
```

### Test on Single File First

```bash
# Test on one file
python3 bin/search_and_replace_directory.py \
    rtl/common/test_file.sv \
    "pattern" \
    "replacement"

# Verify result
cat rtl/common/test_file.sv

# If good, apply to directory
python3 bin/search_and_replace_directory.py \
    rtl/common \
    "pattern" \
    "replacement" \
    --file-extensions .sv
```

### Symbolic Link Protection

The script automatically skips symbolic links to prevent:
- Following circular links
- Modifying files outside target directory
- Breaking link relationships

### Encoding Handling

Uses UTF-8 with error replacement:
- Invalid UTF-8 sequences are replaced with placeholder characters
- Prevents crashes on binary or mixed-encoding files
- May corrupt binary files - use `--file-extensions` to avoid

## Limitations and Considerations

### Known Limitations

1. **In-place Modification:** Files are overwritten without backup
2. **No Multi-line Matching:** Each line is processed independently (by default)
3. **Case Sensitive:** Patterns are case-sensitive by default
4. **No Dry Run:** Cannot preview changes without modification
5. **Binary File Risk:** May corrupt binary files if extension filter not used

### Regex Limitations

1. **Greedy Matching:** Default behavior is greedy (use `?` for non-greedy)
2. **Backslash Escaping:** Special characters need escaping (`\` → `\\`)
3. **Line-based:** Multi-line patterns require special handling

### Performance Considerations

- **Small Projects:** Instant (<1 second for ~100 files)
- **Large Projects:** May take 10-30 seconds for thousands of files
- **Complex Patterns:** Regex complexity affects performance

## Troubleshooting

### Issue: Pattern not matching

**Cause:** Regex special characters not escaped or pattern syntax error

**Solution:**
```bash
# Test pattern first
echo "test string" | grep -P "your_pattern"

# Escape special characters
python3 bin/search_and_replace_directory.py dir "signal\[0\]" "wire[0]"
```

### Issue: Too many files modified

**Cause:** Pattern too broad or missing file extension filter

**Solution:**
```bash
# Add file extension filter
--file-extensions .sv .svh

# Use more specific pattern with word boundaries
"\\bexact_word\\b"
```

### Issue: Encoding errors

**Cause:** Binary files or non-UTF-8 encoding

**Solution:**
```bash
# Use file extension filter to avoid binary files
--file-extensions .sv .py .md

# Or identify problematic files
file * | grep -v "ASCII\|UTF-8"
```

### Issue: Unwanted replacements in comments

**Cause:** Pattern matches in comments as well as code

**Solution:** Use more sophisticated regex to avoid comments (advanced) or manually review changes

## Related Tools

- **[Case Fix](casefix.md)** - Specialized for SystemVerilog case statements
- **[Lint Wrapper](lint_wrap.md)** - Code style and formatting
- **sed/awk** - UNIX text processing tools (alternatives)

## Integration with RTL Design Flow

This tool fits into the refactoring and maintenance phase:

```
Design → Refactoring → Verification → Implementation
           ↑
  search_and_replace_directory.py
```

**Use Cases:**
- Systematic module renaming
- Signal naming convention enforcement
- Import path updates after reorganization
- Copyright and header updates

## Version History

- **Created:** 2025-10-18
- **Author:** sean galloway
- **License:** MIT

---

[Back to Scripts Index](index.md)

---
