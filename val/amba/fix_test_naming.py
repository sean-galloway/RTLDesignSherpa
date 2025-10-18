#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: fix_test_naming
# Purpose: Fix test_name_plus_params naming in all AMBA tests.
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Fix test_name_plus_params naming in all AMBA tests.

Removes "test_" prefix from test_name_plus_params strings.

Pattern: test_name_plus_params = f"test_{dut_name}_..."
Becomes: test_name_plus_params = f"{dut_name}_..."

Usage: python3 fix_test_naming.py [--dry-run]
"""

import re
import sys
import glob
from pathlib import Path

def fix_test_naming(file_path, dry_run=False):
    """Fix test naming in a single file."""
    with open(file_path, 'r') as f:
        content = f.read()
        original = content

    # Pattern 1: test_name_plus_params = f"test_{dut_name}_...
    # Replace with: test_name_plus_params = f"{dut_name}_...
    pattern1 = r'(test_name_plus_params\s*=\s*f")test_\{(dut_name[^}]*)\}'
    replacement1 = r'\1{\2}'
    content, count1 = re.subn(pattern1, replacement1, content)

    # Pattern 2: test_name_plus_params = f"test_<literal>_...
    # Replace with: test_name_plus_params = f"<literal>_...
    pattern2 = r'(test_name_plus_params\s*=\s*f")test_([a-zA-Z0-9_]+_)'
    replacement2 = r'\1\2'
    content, count2 = re.subn(pattern2, replacement2, content)

    total_changes = count1 + count2

    if total_changes > 0:
        if dry_run:
            print(f"[DRY-RUN] {file_path}: {total_changes} change(s) would be made")
        else:
            with open(file_path, 'w') as f:
                f.write(content)
            print(f"[FIXED] {file_path}: {total_changes} change(s)")
        return total_changes

    return 0

def main():
    dry_run = '--dry-run' in sys.argv

    if dry_run:
        print("=" * 80)
        print("DRY RUN MODE - No files will be modified")
        print("=" * 80)

    # Find all test files in current directory
    test_files = sorted(glob.glob('test_*.py'))

    total_files_changed = 0
    total_changes = 0

    for test_file in test_files:
        changes = fix_test_naming(test_file, dry_run)
        if changes > 0:
            total_files_changed += 1
            total_changes += changes

    print("=" * 80)
    if dry_run:
        print(f"SUMMARY (DRY RUN):")
    else:
        print(f"SUMMARY:")
    print(f"  Files processed: {len(test_files)}")
    print(f"  Files changed: {total_files_changed}")
    print(f"  Total changes: {total_changes}")
    print("=" * 80)

    if dry_run:
        print("\nRun without --dry-run to apply changes")

if __name__ == '__main__':
    main()
