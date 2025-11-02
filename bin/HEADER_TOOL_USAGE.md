# File Header Tool - Usage Guide

**Script:** `bin/add_file_headers.py`
**Purpose:** Batch-add MIT license headers to source files

---

## Quick Start

### 1. Preview Changes (Dry Run)

Always run a dry-run first to see what will change:

```bash
# Preview all files
python3 bin/add_file_headers.py --dry-run

# Preview specific directory only
python3 bin/add_file_headers.py --dry-run --dir rtl/amba
```

### 2. Apply Headers

```bash
# Apply to all files (with confirmation prompt)
python3 bin/add_file_headers.py

# Skip confirmation prompt
python3 bin/add_file_headers.py --yes

# Apply to specific directory only
python3 bin/add_file_headers.py --dir projects/components/rapids
```

### 3. Use Minimal Headers

For simple files where full header is too verbose:

```bash
python3 bin/add_file_headers.py --minimal --dry-run
```

---

## Command-Line Options

| Option | Description |
|--------|-------------|
| `--dry-run` | Preview changes without modifying files |
| `--minimal` | Use minimal header format (shorter) |
| `--dir DIR` | Process only specific directory |
| `--yes` `-y` | Skip confirmation prompt |
| `--verbose` `-v` | Show all files including already-processed |

---

## Header Detection

The script **automatically skips files that already have headers** by checking for:
- `SPDX-License-Identifier` in first 500 characters

This means you can safely run the script multiple times - it will only add headers to files that don't have them.

---

## Supported File Types

| Extension | Language | Header Style |
|-----------|----------|--------------|
| `.sv` | SystemVerilog | `// comment` |
| `.svh` | SystemVerilog Header | `// comment` |
| `.py` | Python | `# comment` |

---

## Header Formats

### Full Header (Default)

**SystemVerilog:**
```systemverilog
// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/[your-org]/rtldesignsherpa
//
// Module: scheduler
// Purpose: RAPIDS task scheduler with credit-based flow control
//
// Documentation: projects/components/rapids/docs/rapids_spec/ch02_blocks/01_01_scheduler.md
// Subsystem: rapids
//
// Author: sean galloway
// Created: 2025-10-18
```

**Python:**
```python
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/[your-org]/rtldesignsherpa
#
# Module: SchedulerTB
# Purpose: Scheduler testbench implementation
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids/tests
#
# Author: sean galloway
# Created: 2025-10-18
```

### Minimal Header (`--minimal`)

**SystemVerilog:**
```systemverilog
// SPDX-License-Identifier: MIT
// Copyright (c) 2024-2025 sean galloway
//
// Module: scheduler
// Purpose: RAPIDS task scheduler with credit-based flow control
// Documentation: projects/components/rapids/docs/rapids_spec/ch02_blocks/01_01_scheduler.md
```

**Python:**
```python
# SPDX-License-Identifier: MIT
# Copyright (c) 2024-2025 sean galloway
#
# Module: SchedulerTB
# Purpose: Scheduler testbench implementation
# Documentation: projects/components/rapids/PRD.md
```

---

## What the Script Does

1. **Scans Repository:** Finds all `.sv`, `.svh`, `.py` files
2. **Checks for Headers:** Skips files with existing SPDX headers
3. **Extracts Metadata:**
   - Module name (from `module` keyword or class name)
   - Subsystem (from directory path)
   - Purpose (from existing comments or filename)
   - Documentation path (PRD.md location)
4. **Generates Header:** Creates appropriate header based on file type
5. **Adds Header:** Inserts at top of file (preserving Python shebangs)

---

## Directories Automatically Skipped

- `.git/`
- `__pycache__/`
- `build/`, `sim_build/`, `local_sim_build/`
- `logs/`
- `venv/`, `env/`, `.venv/`
- `node_modules/`
- `.pytest_cache/`, `.mypy_cache/`, `.tox/`

---

## Files Automatically Skipped

- **Symbolic links** (all symlinks are skipped to avoid processing linked files)
- `__init__.py` (usually minimal/auto-generated)
- `conftest.py` (pytest config, often minimal)

---

## Example Workflows

### Add Headers to New Component

```bash
# 1. Create new component RTL and tests
mkdir -p projects/components/mycomponent/rtl
mkdir -p projects/components/mycomponent/dv/tests

# 2. Write your code...

# 3. Preview headers for just this component
python3 bin/add_file_headers.py --dry-run --dir projects/components/mycomponent

# 4. Apply headers
python3 bin/add_file_headers.py --dir projects/components/mycomponent
```

### Update Entire Repository

```bash
# 1. Dry run to see what will change
python3 bin/add_file_headers.py --dry-run

# 2. Review output, then apply
python3 bin/add_file_headers.py --yes
```

### Add Headers to Specific Subsystem

```bash
# AMBA subsystem only
python3 bin/add_file_headers.py --dir rtl/amba

# RAPIDS subsystem only
python3 bin/add_file_headers.py --dir projects/components/rapids

# Tests only
python3 bin/add_file_headers.py --dir val
```

---

## Troubleshooting

### Script Reports "Error reading"

- Check file permissions
- Ensure file encoding is UTF-8
- Check for binary files accidentally in source directories

### Headers Look Wrong

- Run with `--dry-run` first to preview
- Check if file already has non-SPDX header
- Manually verify module name extraction worked

### Want to Update Existing Headers

The script only adds headers to files without them. To update existing headers:

1. Manually remove old header from file
2. Run script to add new header
3. Or use your editor's find/replace to update copyright years

---

## Output Example

```
Scanning for files in: /mnt/data/github/rtldesignsherpa
Found 247 files to process

✓ rtl/amba/shared/axi_monitor_base.sv: Header added
✓ rtl/common/counter_bin.sv: Header added
- rtl/common/fifo_sync.sv: Already has header
✓ projects/components/rapids/rtl/rapids_fub/scheduler.sv: Header added
✗ projects/components/rapids/rtl/bad_file.sv: Error reading: Permission denied

======================================================================
Summary:
  Modified: 187
  Skipped:  58
  Errors:   2
```

---

## Notes

1. **Safe to Run Multiple Times:** Script detects existing headers and won't duplicate
2. **Preserves Python Shebangs:** `#!/usr/bin/env python3` lines preserved
3. **Auto-Detects Module Names:** Extracts from `module` keyword or class name
4. **Smart Documentation Paths:** Links to appropriate PRD.md for subsystem
5. **Dry-Run Always Safe:** Use `--dry-run` liberally to preview changes

---

## Future Enhancements

If you need to:
- Update copyright years in existing headers
- Change author name in existing headers
- Switch from minimal to full headers

Create a separate script or use find/replace in your editor.

---

**Version:** 1.0
**Last Updated:** 2025-10-18
**Author:** sean galloway
