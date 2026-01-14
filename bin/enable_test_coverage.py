#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 Qernel AI
#
# Script to add coverage support to CocoTB test files
#
# Usage:
#   ./bin/enable_test_coverage.py --check     # Show which files need updating
#   ./bin/enable_test_coverage.py --apply     # Apply changes to all files
#   ./bin/enable_test_coverage.py --file X    # Update a specific file
#   ./bin/enable_test_coverage.py --test-dirs dir1 dir2  # Specify test directories

"""
Add Coverage Support to CocoTB Test Files

This script modifies CocoTB test files to enable Verilator coverage collection.
It adds:
1. Import for get_coverage_compile_args
2. Call to extend compile_args with coverage flags

The changes are idempotent - running multiple times won't duplicate changes.
Works with any CocoTB project by specifying test directories.
"""

import argparse
import os
import re
import sys
from pathlib import Path
from typing import List, Tuple

# Default test directories (can be overridden via CLI)
DEFAULT_TEST_DIRS = [
    'design_dv/tests/fub',
    'design_dv/tests/macro',
]

# Import line to add - uses generic path that works with any project
# Projects should ensure coverage_utils.py is available in PYTHONPATH
COVERAGE_IMPORT = "from CocoTBFramework.components.coverage_utils import get_coverage_compile_args"

# Line to add after compile_args definition
COVERAGE_EXTEND = "    # Add coverage flags when COVERAGE=1 is set\n    compile_args.extend(get_coverage_compile_args())"


def find_test_files(base_dir: str, test_dirs: List[str] = None) -> List[Path]:
    """Find all test_*.py files in specified directories"""
    if test_dirs is None:
        test_dirs = DEFAULT_TEST_DIRS
    test_files = []
    for test_dir in test_dirs:
        full_dir = Path(base_dir) / test_dir
        if full_dir.exists():
            test_files.extend(full_dir.glob('test_*.py'))
    return sorted(test_files)


def check_file_needs_update(filepath: Path) -> Tuple[bool, bool, str]:
    """Check if a file needs coverage support added

    Returns:
        (needs_import, needs_extend, reason)
    """
    content = filepath.read_text()

    has_import = 'get_coverage_compile_args' in content
    has_extend = 'compile_args.extend(get_coverage_compile_args())' in content
    has_compile_args = 'compile_args = [' in content

    if not has_compile_args:
        return False, False, "No compile_args found"

    needs_import = not has_import
    needs_extend = not has_extend

    if not needs_import and not needs_extend:
        return False, False, "Already has coverage support"

    return needs_import, needs_extend, "Needs update"


def update_file(filepath: Path, dry_run: bool = False) -> bool:
    """Update a test file to add coverage support

    Returns:
        True if changes were made
    """
    content = filepath.read_text()
    original_content = content
    changes_made = False

    needs_import, needs_extend, reason = check_file_needs_update(filepath)

    if not needs_import and not needs_extend:
        return False

    # Add import if needed
    if needs_import:
        # Find the TBBase import line and add after it
        patterns = [
            (r'(from CocoTBFramework\.tbclasses\.shared\.tbbase import TBBase\n)',
             r'\1\n# Coverage utilities\n' + COVERAGE_IMPORT + '\n'),
            # Alternative: after any framework import
            (r'(from CocoTBFramework\.[^\n]+\n)(\n# ==)',
             r'\1\n# Coverage utilities\n' + COVERAGE_IMPORT + r'\n\2'),
        ]

        for pattern, replacement in patterns:
            if re.search(pattern, content):
                content = re.sub(pattern, replacement, content, count=1)
                changes_made = True
                break

    # Add extend call if needed
    if needs_extend:
        # Find compile_args = [...] and add extend after it
        # Match the closing bracket of compile_args list
        pattern = r'(compile_args = \[\n(?:[^\]]+)\n    \])'
        match = re.search(pattern, content)

        if match:
            old_block = match.group(1)
            new_block = old_block + '\n' + COVERAGE_EXTEND
            content = content.replace(old_block, new_block, 1)
            changes_made = True

    if changes_made and content != original_content:
        if not dry_run:
            filepath.write_text(content)
            print(f"  Updated: {filepath}")
        else:
            print(f"  Would update: {filepath}")
        return True

    return False


def main():
    parser = argparse.ArgumentParser(description='Add coverage support to CocoTB test files')
    parser.add_argument('--check', action='store_true', help='Check which files need updating')
    parser.add_argument('--apply', action='store_true', help='Apply changes to all files')
    parser.add_argument('--file', type=str, help='Update a specific file')
    parser.add_argument('--dry-run', action='store_true', help='Show what would be changed')
    parser.add_argument('--test-dirs', type=str, nargs='+',
                        help='Test directories relative to repo root (default: design_dv/tests/fub design_dv/tests/macro)')

    args = parser.parse_args()

    # Find repo root
    script_dir = Path(__file__).parent
    repo_root = script_dir.parent

    # Use provided test dirs or defaults
    test_dirs = args.test_dirs if args.test_dirs else None

    if args.file:
        # Update single file
        filepath = Path(args.file)
        if not filepath.exists():
            print(f"Error: File not found: {filepath}")
            sys.exit(1)

        needs_import, needs_extend, reason = check_file_needs_update(filepath)
        if needs_import or needs_extend:
            update_file(filepath, dry_run=args.dry_run)
        else:
            print(f"File already has coverage support: {filepath}")

    elif args.check:
        # Check all files
        test_files = find_test_files(repo_root, test_dirs)
        print(f"Checking {len(test_files)} test files...\n")

        needs_update = []
        already_done = []

        for filepath in test_files:
            needs_import, needs_extend, reason = check_file_needs_update(filepath)
            if needs_import or needs_extend:
                needs_update.append((filepath, reason))
            elif 'compile_args' in filepath.read_text():
                already_done.append(filepath)

        if needs_update:
            print("Files needing coverage support:")
            for filepath, reason in needs_update:
                print(f"  - {filepath.relative_to(repo_root)}: {reason}")
        else:
            print("All test files have coverage support!")

        print(f"\nSummary: {len(needs_update)} need update, {len(already_done)} already done")

    elif args.apply:
        # Apply to all files
        test_files = find_test_files(repo_root, test_dirs)
        print(f"Processing {len(test_files)} test files...\n")

        updated = 0
        for filepath in test_files:
            if update_file(filepath, dry_run=args.dry_run):
                updated += 1

        print(f"\n{'Would update' if args.dry_run else 'Updated'} {updated} files")

    else:
        parser.print_help()


if __name__ == '__main__':
    main()
