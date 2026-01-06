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

# PyTree

## Overview

The `pytree.py` script is a pure-Python implementation of the UNIX `tree` command for visualizing directory structures. It recursively displays files and subdirectories in a hierarchical tree format with customizable filtering capabilities.

**Location:** `bin/pytree.py`

**Purpose:** Generate directory tree visualizations with optional exclusion filters

**Key Features:**
- Recursive directory traversal
- Customizable file and directory exclusions
- Clean tree-style formatting with ASCII art
- Files displayed before directories (organized layout)
- No external dependencies

## Usage

### Command Line Arguments

```bash
python3 bin/pytree.py --path <directory> [options]
```

### Required Arguments

| Argument | Description |
|----------|-------------|
| `--path` | Root directory to display |

### Optional Arguments

| Argument | Description |
|----------|-------------|
| `--exclude-dir` | Space-separated list of directory names to exclude |
| `--exclude-file` | Space-separated list of file names to exclude |

## Examples

### Example 1: Basic Directory Tree

```bash
python3 bin/pytree.py --path rtl/common
```

**Output:**
```
rtl/common
├── arbiter_round_robin.sv
├── counter_bin.sv
├── fifo_sync.sv
├── README.md
├── PRD.md
└── subdir
    ├── module1.sv
    └── module2.sv
```

### Example 2: Excluding Directories

```bash
python3 bin/pytree.py --path . --exclude-dir __pycache__ .git build
```

**Output:** Shows all files and directories except `__pycache__`, `.git`, and `build`

### Example 3: Excluding Specific Files

```bash
python3 bin/pytree.py --path val/common --exclude-file Makefile setup.py
```

**Output:** Shows directory tree without `Makefile` or `setup.py` files

### Example 4: Comprehensive Filtering

```bash
python3 bin/pytree.py \
    --path CocoTBFramework \
    --exclude-dir __pycache__ .pytest_cache build dist \
    --exclude-file .DS_Store *.pyc
```

**Output:** Clean tree view without build artifacts, cache files, or system files

### Example 5: RTL Subsystem Overview

```bash
python3 bin/pytree.py \
    --path rtl/amba \
    --exclude-dir sim_build __pycache__ \
    --exclude-file *.vcd *.fst
```

**Output:** RTL directory structure without simulation outputs

## Output Format

### Tree Structure Symbols

The script uses ASCII characters to create the tree visualization:

| Symbol | Meaning |
|--------|---------|
| `├──` | Branch (more items follow) |
| `└──` | Last branch (final item in list) |
| `│   ` | Vertical continuation line |
| `    ` | Indent for nested items |

### Display Order

Within each directory level:
1. **Files first** - Sorted alphabetically
2. **Directories second** - Sorted alphabetically

This differs from the UNIX `tree` command (which mixes files and directories) but provides better readability for RTL projects.

## How It Works

### Processing Flow

```
1. Validate root directory exists
   ↓
2. Print root directory path
   ↓
3. Call print_tree() recursively
   ↓
4. For current directory:
   ├── Get all items
   ├── Filter excluded items
   ├── Separate files and directories
   ├── Sort each group alphabetically
   ├── Display files with tree symbols
   ├── Display directories with tree symbols
   └── Recurse into each subdirectory
```

### Recursive Algorithm

```python
def print_tree(directory, prefix="", exclude_dirs=None, exclude_files=None):
    # Filter items
    all_items = [p for p in directory.iterdir()
                 if p.name not in exclude_dirs
                 and p.name not in exclude_files]

    # Separate and sort
    files = sorted([item for item in all_items if item.is_file()])
    directories = sorted([item for item in all_items if item.is_dir()])

    # Display files
    for index, item in enumerate(files):
        connector = "├── " if (index < len(files) - 1 or directories) else "└── "
        print(prefix + connector + item.name)

    # Display and recurse directories
    for index, item in enumerate(directories):
        connector = "└── " if index == len(directories) - 1 else "├── "
        print(prefix + connector + item.name)

        extension = "    " if index == len(directories) - 1 else "│   "
        print_tree(item, prefix + extension, exclude_dirs, exclude_files)
```

## Use Cases

### 1. Documentation Generation

Create directory structure for README files:

```bash
python3 bin/pytree.py --path rtl/amba --exclude-dir sim_build > rtl/amba/STRUCTURE.txt
```

### 2. Project Overview

Quick visualization of repository structure:

```bash
python3 bin/pytree.py \
    --path . \
    --exclude-dir __pycache__ .git node_modules venv build dist sim_build \
    --exclude-file .DS_Store *.pyc
```

### 3. Subsystem Analysis

Understand RTL organization:

```bash
# View AMBA subsystem structure
python3 bin/pytree.py --path rtl/amba

# View test structure
python3 bin/pytree.py --path val/amba
```

### 4. Filtering Build Artifacts

Clean view without temporary files:

```bash
python3 bin/pytree.py \
    --path projects/components/bridge \
    --exclude-dir sim_build __pycache__ \
    --exclude-file *.vcd *.fst *.log
```

### 5. Comparing Structures

Compare different subsystem organizations:

```bash
python3 bin/pytree.py --path rtl/common > common_structure.txt
python3 bin/pytree.py --path rtl/amba > amba_structure.txt
diff common_structure.txt amba_structure.txt
```

## Advanced Usage

### Integration with grep

```bash
# Find all Python files in tree
python3 bin/pytree.py --path CocoTBFramework | grep "\.py$"

# Count SystemVerilog files
python3 bin/pytree.py --path rtl | grep -c "\.sv$"
```

### Redirect to Documentation

```bash
# Generate structure documentation
cat > rtl/common/DIRECTORY_STRUCTURE.md <<EOF
# Common RTL Directory Structure

\`\`\`
$(python3 bin/pytree.py --path rtl/common --exclude-dir sim_build)
\`\`\`
EOF
```

### Find Largest Directories

```bash
# Show first few levels to identify large directories
python3 bin/pytree.py --path . --exclude-dir __pycache__ .git | head -50
```

### Create Archive of Structure

```bash
# Document structure before major refactoring
python3 bin/pytree.py --path . --exclude-dir build sim_build > structure_$(date +%Y%m%d).txt
```

## Comparison with UNIX `tree`

### Differences

| Feature | pytree.py | UNIX tree |
|---------|-----------|-----------|
| **Dependencies** | Pure Python | System binary |
| **Display Order** | Files first, dirs second | Mixed |
| **Filtering** | By name only | By pattern, attributes |
| **File Counts** | Not shown | Optional |
| **Colors** | No | Yes (with -C) |
| **Portability** | Cross-platform | Platform-specific |

### When to Use pytree.py

Use `pytree.py` when:
- UNIX `tree` is not available
- You need files-first display order
- You're scripting in Python
- You want consistent behavior across platforms

### When to Use UNIX tree

Use `tree` when:
- Advanced filtering (patterns, permissions, dates)
- File size/count statistics
- Colored output
- Performance is critical (very large directories)

## Technical Details

### Path Handling

Uses Python's `pathlib.Path` for cross-platform compatibility:

```python
from pathlib import Path

root_dir = Path(args.path)
for item in directory.iterdir():
    if item.is_file(): ...
    if item.is_dir(): ...
```

### Sorting

Alphabetical sorting uses Python's default string comparison:

```python
files = sorted([item for item in all_items if item.is_file()])
directories = sorted([item for item in all_items if item.is_dir()])
```

### Exclusion Matching

Simple set membership check:

```python
exclude_dirs = set(exclude_dirs or [])
exclude_files = set(exclude_files or [])

all_items = [p for p in directory.iterdir()
             if p.name not in exclude_dirs
             and p.name not in exclude_files]
```

## Limitations and Considerations

### Known Limitations

1. **No Pattern Matching:** Exclusions are exact name matches only, not glob patterns
2. **No Symlink Handling:** Symbolic links are treated as regular files/directories
3. **No File Metadata:** Doesn't show sizes, permissions, or modification dates
4. **No Color Output:** Plain ASCII output only
5. **Debug Output:** Contains `DEBUG:` print statement that should be removed for production

### Performance Considerations

- **Small to Medium Projects:** Instant results (<1 second for ~1000 files)
- **Large Projects:** May take several seconds for directories with >10,000 files
- **Deep Nesting:** No practical limit on recursion depth (uses Python's default)

### Best Practices

1. **Use Exclusions:** Always exclude build artifacts and caches for cleaner output
2. **Redirect Large Outputs:** Pipe to `less` or redirect to file for large directories
3. **Document Structures:** Save tree outputs when documenting refactoring or reorganization

## Troubleshooting

### Issue: Permission denied errors

**Cause:** Trying to access directories without read permissions

**Solution:**
```bash
# Run with appropriate permissions or exclude protected directories
python3 bin/pytree.py --path /restricted --exclude-dir protected_dir
```

### Issue: Too much output

**Cause:** Large directory tree without exclusions

**Solutions:**
```bash
# Add exclusions
python3 bin/pytree.py --path . --exclude-dir build __pycache__ .git

# Pipe to less for pagination
python3 bin/pytree.py --path . | less

# Limit depth with head
python3 bin/pytree.py --path . | head -100
```

### Issue: Symlinks create loops

**Cause:** Circular symbolic links

**Solution:** Modify script to detect and break symlink cycles, or exclude problematic directories

### Issue: DEBUG output appears

**Cause:** Debug print statement in code (line 56)

**Solution:** Comment out or remove the line:
```python
# print(f"DEBUG: exclude_dir = {args.exclude_dir}")
```

## Related Tools

- **[Search and Replace Directory](search_and_replace_directory.md)** - Recursive file processing
- **[Find Instances Used](find_instances_used.md)** - Dependency analysis
- **UNIX `tree`** - System directory tree command

## Integration with RTL Design Flow

This tool fits into the documentation phase:

```
Design → Analysis → Documentation → Implementation
                          ↑
                      pytree.py
```

**Use Cases:**
- Document directory structure in README files
- Verify organization after refactoring
- Create visual guides for new contributors
- Track structural changes over time

## Version History

- **Created:** 2025-10-18
- **Author:** sean galloway
- **License:** MIT

---

[Back to Scripts Index](index.md)

---
