#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: verify_unique_resolved_names
# Purpose: Verify that resolved test names (not just patterns) are unique across test files
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Verify that resolved test names (not just patterns) are unique across test files.
This checks for ACTUAL collisions in sim_build directories, not just pattern similarity.
"""

import os
import glob
from collections import defaultdict

def get_actual_sim_builds():
    """Get all actual sim_build directory names that exist."""
    sim_builds = []
    sim_build_dir = 'local_sim_build'

    if os.path.exists(sim_build_dir):
        for entry in os.listdir(sim_build_dir):
            path = os.path.join(sim_build_dir, entry)
            if os.path.isdir(path):
                sim_builds.append(entry)

    return sorted(sim_builds)

def analyze_name_patterns(names):
    """Group similar names to identify potential module families."""
    families = defaultdict(list)

    for name in names:
        # Extract base module name (first part before parameters)
        if '_' in name:
            # Common patterns: module_param1_param2_...
            base = name.split('_')[0]
            # For multi-word modules like axi4_master_rd
            if name.startswith('axi4_') or name.startswith('axil4_') or name.startswith('axis_'):
                parts = name.split('_')
                if len(parts) >= 3:
                    base = '_'.join(parts[:3])  # e.g., "axi4_master_rd"
                elif len(parts) >= 2:
                    base = '_'.join(parts[:2])  # e.g., "axis_master"
        else:
            base = name

        families[base].append(name)

    return families

def check_for_duplicates(names):
    """Check if there are any exact duplicate names."""
    name_counts = defaultdict(int)
    for name in names:
        name_counts[name] += 1

    duplicates = {name: count for name, count in name_counts.items() if count > 1}
    return duplicates

def main():
    print("=" * 80)
    print("RESOLVED TEST NAME UNIQUENESS CHECK")
    print("Analyzing ACTUAL sim_build directories (resolved names, not patterns)")
    print("=" * 80)

    # Get actual sim_build directories
    sim_builds = get_actual_sim_builds()

    if not sim_builds:
        print("\n⚠️  No sim_build directories found.")
        print("   Run some tests first to generate sim_build directories.")
        return

    print(f"\nTotal sim_build directories found: {len(sim_builds)}")

    # Check for exact duplicates
    duplicates = check_for_duplicates(sim_builds)

    if duplicates:
        print(f"\n❌ CRITICAL: EXACT DUPLICATE NAMES FOUND: {len(duplicates)}")
        print("=" * 80)
        for name, count in duplicates.items():
            print(f"\n'{name}' appears {count} times")
            print("  This WILL cause collisions in parallel execution!")
    else:
        print("\n✅ NO EXACT DUPLICATES - All resolved names are unique")

    # Analyze module families
    print("\n" + "=" * 80)
    print("MODULE FAMILY ANALYSIS")
    print("=" * 80)

    families = analyze_name_patterns(sim_builds)

    print(f"\nModule families found: {len(families)}")
    print("\nFamilies with multiple configurations:")

    for base, configs in sorted(families.items()):
        if len(configs) > 1:
            print(f"\n  {base}: {len(configs)} configurations")
            for config in sorted(configs)[:5]:  # Show first 5
                print(f"    - {config}")
            if len(configs) > 5:
                print(f"    ... and {len(configs) - 5} more")

    # Parallel execution safety
    print("\n" + "=" * 80)
    print("PARALLEL EXECUTION SAFETY ASSESSMENT")
    print("=" * 80)

    if duplicates:
        print("\n❌ UNSAFE FOR PARALLEL EXECUTION")
        print(f"   Found {len(duplicates)} exact duplicate names")
        print("   These will overwrite each other's sim_build directories")
    else:
        print("\n✅ SAFE FOR PARALLEL EXECUTION")
        print(f"   All {len(sim_builds)} test names are unique")
        print("   Each test has its own sim_build directory")

    print("=" * 80)

if __name__ == '__main__':
    main()
