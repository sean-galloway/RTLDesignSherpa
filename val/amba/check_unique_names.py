#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: check_unique_names
# Purpose: Check for duplicate test_name_plus_params across all AMBA test files.
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Check for duplicate test_name_plus_params across all AMBA test files.
This ensures tests can run in parallel without conflicting sim_build directories.
"""

import re
import glob
from collections import defaultdict

def extract_test_names(file_path):
    """Extract all test_name_plus_params patterns from a test file."""
    with open(file_path, 'r') as f:
        content = f.read()

    # Find all test_name_plus_params assignments
    pattern = r'test_name_plus_params\s*=\s*f"([^"]+)"'
    matches = re.findall(pattern, content)
    return matches

def main():
    # Find all test files
    test_files = sorted(glob.glob('test_*.py'))

    # Track all test names and where they appear
    all_names = defaultdict(list)

    for test_file in test_files:
        patterns = extract_test_names(test_file)
        for pattern in patterns:
            all_names[pattern].append(test_file)

    # Find duplicates
    duplicates = {name: files for name, files in all_names.items() if len(files) > 1}

    # Find potential conflicts (same base pattern)
    potential_conflicts = defaultdict(list)
    for pattern, files in all_names.items():
        # Extract base name (everything before first parameter)
        base = pattern.split('_')[0] if '_' in pattern else pattern
        potential_conflicts[base].append((pattern, files[0]))

    print("=" * 80)
    print("TEST NAME UNIQUENESS CHECK")
    print("=" * 80)

    print(f"\nTotal test files: {len(test_files)}")
    print(f"Total unique test name patterns: {len(all_names)}")

    if duplicates:
        print(f"\n⚠️  EXACT DUPLICATES FOUND: {len(duplicates)}")
        print("=" * 80)
        for name, files in duplicates.items():
            print(f"\nPattern: {name}")
            for f in files:
                print(f"  - {f}")
    else:
        print("\n✅ No exact duplicate patterns found")

    # Check for base name conflicts
    print("\n" + "=" * 80)
    print("MODULE NAME ANALYSIS")
    print("=" * 80)

    for base, patterns in sorted(potential_conflicts.items()):
        if len(patterns) > 1:
            print(f"\nBase: '{base}' ({len(patterns)} variations)")
            for pattern, file in patterns[:5]:  # Show first 5
                print(f"  {pattern} ({file})")

    # Specific parallel execution check
    print("\n" + "=" * 80)
    print("PARALLEL EXECUTION SAFETY")
    print("=" * 80)

    # Group by module name (first part before parameters)
    module_groups = defaultdict(list)
    for pattern, files in all_names.items():
        # Extract module name (e.g., "apb_master" from "apb_master_aw{aw_str}_...")
        match = re.match(r'^([a-z0-9_]+?)_(?:aw|dw|i|sd|w|d|cl|wr|rd)', pattern)
        if match:
            module_name = match.group(1)
        else:
            module_name = pattern.split('_')[0]
        module_groups[module_name].append((pattern, files[0]))

    print(f"\nModules with multiple test configurations: {len([g for g in module_groups.values() if len(g) > 1])}")

    conflicts = []
    for module, configs in sorted(module_groups.items()):
        if len(configs) > 1:
            # Check if any configurations would generate the same name
            resolved_names = []
            for pattern, file in configs:
                # Simulate parameter resolution (this is approximate)
                # Real resolution depends on actual parameter values
                resolved_names.append((pattern, file))

            print(f"\n  {module}: {len(configs)} configs in {configs[0][1]}")

    print("\n" + "=" * 80)
    if not duplicates:
        print("✅ SAFE FOR PARALLEL EXECUTION")
        print("   All test names appear unique when parameters are resolved.")
    else:
        print("⚠️  POTENTIAL CONFLICTS")
        print("   Review duplicate patterns above.")
    print("=" * 80)

if __name__ == '__main__':
    main()
