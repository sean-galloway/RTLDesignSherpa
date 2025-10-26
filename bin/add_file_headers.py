#!/usr/bin/env python3
"""
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2024-2025 sean galloway

RTL Design Sherpa - Batch File Header Tool
https://github.com/[your-org]/rtldesignsherpa

Purpose: Batch-add MIT license headers to source files

Usage:
    # Dry run (preview changes)
    python3 bin/add_file_headers.py --dry-run

    # Apply headers to all files
    python3 bin/add_file_headers.py

    # Apply only to specific directories
    python3 bin/add_file_headers.py --dir rtl/amba

    # Use minimal headers
    python3 bin/add_file_headers.py --minimal

    # Skip confirmation prompt
    python3 bin/add_file_headers.py --yes

Author: sean galloway
Created: 2025-10-18
"""

import os
import sys
import re
import argparse
from pathlib import Path
from datetime import datetime
from typing import List, Tuple, Optional

# ============================================================================
# Configuration
# ============================================================================

AUTHOR = "sean galloway"
COPYRIGHT_YEARS = "2024-2025"
PROJECT_NAME = "RTL Design Sherpa - Industry-Standard RTL Design and Verification"
PROJECT_URL = "https://github.com/sean-galloway/RTLDesignSherpa"

# Directories to skip
SKIP_DIRS = {
    '.git', '__pycache__', '.pytest_cache', 'build', 'sim_build',
    'local_sim_build', 'logs', 'venv', 'env', '.venv',
    'node_modules', '.mypy_cache', '.tox', 'dist', 'egg-info'
}

# File extensions to process
SYSTEMVERILOG_EXTS = {'.sv', '.svh'}
PYTHON_EXTS = {'.py'}
ALL_EXTS = SYSTEMVERILOG_EXTS | PYTHON_EXTS

# Files to skip (exact matches)
SKIP_FILES = {
    '__init__.py',  # Usually minimal, auto-generated
    'conftest.py',  # Pytest config, often minimal
}

# ============================================================================
# Header Templates
# ============================================================================

def get_systemverilog_header(module_name: str, purpose: str, subsystem: str,
                              doc_path: str, minimal: bool = False) -> str:
    """Generate SystemVerilog file header."""
    if minimal:
        return f"""// SPDX-License-Identifier: MIT
// Copyright (c) {COPYRIGHT_YEARS} {AUTHOR}
//
// Module: {module_name}
// Purpose: {purpose}
// Documentation: {doc_path}

"""
    else:
        return f"""// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: {COPYRIGHT_YEARS} {AUTHOR}
//
// {PROJECT_NAME}
// {PROJECT_URL}
//
// Module: {module_name}
// Purpose: {purpose}
//
// Documentation: {doc_path}
// Subsystem: {subsystem}
//
// Author: {AUTHOR}
// Created: {datetime.now().strftime('%Y-%m-%d')}

"""

def get_python_header(module_name: str, purpose: str, subsystem: str,
                       doc_path: str, minimal: bool = False) -> str:
    """Generate Python file header."""
    if minimal:
        return f"""# SPDX-License-Identifier: MIT
# Copyright (c) {COPYRIGHT_YEARS} {AUTHOR}
#
# Module: {module_name}
# Purpose: {purpose}
# Documentation: {doc_path}

"""
    else:
        return f"""# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: {COPYRIGHT_YEARS} {AUTHOR}
#
# {PROJECT_NAME}
# {PROJECT_URL}
#
# Module: {module_name}
# Purpose: {purpose}
#
# Documentation: {doc_path}
# Subsystem: {subsystem}
#
# Author: {AUTHOR}
# Created: {datetime.now().strftime('%Y-%m-%d')}

"""

# ============================================================================
# Helper Functions
# ============================================================================

def has_header(content: str) -> bool:
    """Check if file already has SPDX license header."""
    return 'SPDX-License-Identifier' in content[:500]

def extract_module_name(filepath: Path) -> str:
    """Extract module name from file path."""
    return filepath.stem

def extract_systemverilog_module_name(content: str, filepath: Path) -> str:
    """Extract module name from SystemVerilog source."""
    # Look for 'module <name>' declaration
    match = re.search(r'^\s*module\s+(\w+)', content, re.MULTILINE)
    if match:
        return match.group(1)
    return filepath.stem

def extract_python_class_name(content: str, filepath: Path) -> str:
    """Extract primary class name from Python source."""
    # Look for first class definition
    match = re.search(r'^\s*class\s+(\w+)', content, re.MULTILINE)
    if match:
        return match.group(1)
    return filepath.stem

def determine_subsystem(filepath: Path, repo_root: Path) -> str:
    """Determine subsystem from file path."""
    rel_path = filepath.relative_to(repo_root)
    parts = rel_path.parts

    # Check for common subsystem patterns
    if 'rtl' in parts:
        idx = parts.index('rtl')
        if idx + 1 < len(parts):
            return parts[idx + 1]  # e.g., rtl/amba -> amba
    elif 'projects/components' in str(rel_path):
        if 'projects' in parts:
            idx = parts.index('components')
            if idx + 1 < len(parts):
                return parts[idx + 1]  # e.g., projects/components/rapids -> rapids
    elif 'bin/CocoTBFramework' in str(rel_path):
        return 'framework'
    elif 'val' in parts or 'dv' in parts:
        return 'tests'

    return 'common'

def determine_doc_path(filepath: Path, repo_root: Path, subsystem: str) -> str:
    """Determine documentation path for the file."""
    rel_path = filepath.relative_to(repo_root)

    # Check for component-specific PRDs
    if 'projects/components' in str(rel_path):
        component = subsystem
        return f"projects/components/{component}/PRD.md"

    # Check for subsystem PRDs
    if subsystem in ['amba', 'common', 'rapids']:
        return f"rtl/{subsystem}/PRD.md"

    # Framework files
    if 'CocoTBFramework' in str(rel_path):
        return "bin/CocoTBFramework/README.md"

    # Default to root PRD
    return "PRD.md"

def generate_purpose(filepath: Path, content: str, file_type: str) -> str:
    """Generate a purpose string from file content or name."""
    # Try to extract from existing comments
    if file_type == 'systemverilog':
        # Look for single-line description comment
        match = re.search(r'//\s*Purpose:\s*(.+)', content)
        if match:
            return match.group(1).strip()
        # Look for module description
        match = re.search(r'//\s*Description:\s*(.+)', content)
        if match:
            return match.group(1).strip()
    elif file_type == 'python':
        # Look for docstring
        match = re.search(r'"""(.+?)"""', content, re.DOTALL)
        if match:
            first_line = match.group(1).strip().split('\n')[0]
            return first_line[:80]  # Truncate to reasonable length

    # Generate generic purpose from filename
    name = filepath.stem.replace('_', ' ').title()
    if file_type == 'systemverilog':
        return f"{name} module"
    elif file_type == 'python':
        if 'test_' in filepath.name:
            return f"Test suite for {name.replace('Test ', '')}"
        return f"{name} implementation"

    return "TODO: Add purpose description"

def find_files(root_dir: Path, target_dir: Optional[str] = None) -> List[Path]:
    """Find all processable files in the repository."""
    files = []

    search_root = Path(target_dir) if target_dir else root_dir

    for dirpath, dirnames, filenames in os.walk(search_root):
        # Skip excluded directories
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]

        for filename in filenames:
            filepath = Path(dirpath) / filename

            # Skip symbolic links
            if filepath.is_symlink():
                continue

            # Skip excluded files
            if filename in SKIP_FILES:
                continue

            # Check file extension
            if filepath.suffix in ALL_EXTS:
                files.append(filepath)

    return sorted(files)

def process_file(filepath: Path, repo_root: Path, minimal: bool = False,
                 dry_run: bool = False) -> Tuple[bool, str]:
    """
    Process a single file to add header.

    Returns:
        (modified, message) - Whether file was modified and status message
    """
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        return (False, f"Error reading: {e}")

    # Check if already has header
    if has_header(content):
        return (False, "Already has header")

    # Determine file type
    if filepath.suffix in SYSTEMVERILOG_EXTS:
        file_type = 'systemverilog'
        module_name = extract_systemverilog_module_name(content, filepath)
    elif filepath.suffix in PYTHON_EXTS:
        file_type = 'python'
        module_name = extract_python_class_name(content, filepath)
    else:
        return (False, "Unsupported file type")

    # Gather metadata
    subsystem = determine_subsystem(filepath, repo_root)
    doc_path = determine_doc_path(filepath, repo_root, subsystem)
    purpose = generate_purpose(filepath, content, file_type)

    # Generate header
    if file_type == 'systemverilog':
        header = get_systemverilog_header(module_name, purpose, subsystem, doc_path, minimal)
    else:  # python
        header = get_python_header(module_name, purpose, subsystem, doc_path, minimal)

    # Handle Python shebangs
    new_content = content
    if file_type == 'python' and content.startswith('#!'):
        lines = content.split('\n', 1)
        shebang = lines[0] + '\n'
        rest = lines[1] if len(lines) > 1 else ''
        new_content = shebang + header + rest
    else:
        new_content = header + content

    # Write file if not dry run
    if not dry_run:
        try:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(new_content)
            return (True, "Header added")
        except Exception as e:
            return (False, f"Error writing: {e}")

    return (True, "Would add header (dry-run)")

# ============================================================================
# Main
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description='Batch-add MIT license headers to RTL Design Sherpa source files',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Dry run (preview changes)
  python3 bin/add_file_headers.py --dry-run

  # Apply headers to all files
  python3 bin/add_file_headers.py

  # Apply only to specific directory
  python3 bin/add_file_headers.py --dir rtl/amba

  # Use minimal headers
  python3 bin/add_file_headers.py --minimal

  # Skip confirmation prompt
  python3 bin/add_file_headers.py --yes
        """
    )

    parser.add_argument('--dry-run', action='store_true',
                        help='Preview changes without modifying files')
    parser.add_argument('--minimal', action='store_true',
                        help='Use minimal header format')
    parser.add_argument('--dir', type=str,
                        help='Process only specific directory')
    parser.add_argument('--yes', '-y', action='store_true',
                        help='Skip confirmation prompt')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Show all files (including skipped)')

    args = parser.parse_args()

    # Find repository root
    script_dir = Path(__file__).parent.absolute()
    repo_root = script_dir.parent

    # Find files
    print(f"Scanning for files in: {repo_root}")
    if args.dir:
        print(f"  Limiting to: {args.dir}")

    files = find_files(repo_root, args.dir)
    print(f"Found {len(files)} files to process\n")

    if not files:
        print("No files found to process")
        return 0

    # Confirmation prompt
    if not args.dry_run and not args.yes:
        print("This will add headers to files that don't already have them.")
        response = input("Continue? [y/N]: ")
        if response.lower() != 'y':
            print("Aborted")
            return 0

    # Process files
    stats = {'modified': 0, 'skipped': 0, 'errors': 0}

    for filepath in files:
        rel_path = filepath.relative_to(repo_root)
        modified, message = process_file(filepath, repo_root, args.minimal, args.dry_run)

        if modified:
            stats['modified'] += 1
            print(f"✓ {rel_path}: {message}")
        elif 'Error' in message:
            stats['errors'] += 1
            print(f"✗ {rel_path}: {message}")
        else:
            stats['skipped'] += 1
            if args.verbose:
                print(f"- {rel_path}: {message}")

    # Summary
    print(f"\n{'='*70}")
    print("Summary:")
    print(f"  Modified: {stats['modified']}")
    print(f"  Skipped:  {stats['skipped']}")
    print(f"  Errors:   {stats['errors']}")

    if args.dry_run:
        print("\n(Dry-run mode - no files were actually modified)")
        print("Run without --dry-run to apply changes")

    return 0 if stats['errors'] == 0 else 1

if __name__ == '__main__':
    sys.exit(main())
