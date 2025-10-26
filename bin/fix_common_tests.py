#!/usr/bin/env python3
"""
Remove AMBA includes from val/common tests that don't need them.

The update_test_runners.py script incorrectly added rtl/amba/includes to ALL tests.
Common module tests (arbiters, counters, FIFOs, etc.) don't need AMBA includes.
"""

import re
from pathlib import Path

def fix_test_file(path: Path) -> bool:
    """Remove AMBA includes from a test file. Returns True if modified."""
    text = path.read_text(encoding="utf-8")

    # Check if file has AMBA includes
    if "'rtl_amba_includes'" not in text and '"rtl_amba_includes"' not in text:
        return False  # Nothing to fix

    original_text = text

    # Pattern 1: Remove from get_paths() dict
    # Match: , 'rtl_amba_includes': 'rtl/amba/includes'
    text = re.sub(
        r",\s*['\"]rtl_amba_includes['\"]\s*:\s*['\"]rtl/amba/includes['\"]",
        "",
        text
    )

    # Pattern 2: Fix includes variable
    # Change: includes = [rtl_dict['rtl_amba_includes']]
    # To: includes = []
    text = re.sub(
        r"includes\s*=\s*\[rtl_dict\[['\"]rtl_amba_includes['\"]\]\]",
        "includes = []",
        text
    )

    if text != original_text:
        path.write_text(text, encoding="utf-8")
        return True
    return False

def main():
    val_common = Path("val/common")

    if not val_common.exists():
        print(f"ERROR: {val_common} not found. Run from repo root.")
        return

    test_files = sorted(val_common.glob("test_*.py"))

    print(f"Checking {len(test_files)} test files in val/common...")

    fixed = 0
    for tf in test_files:
        if fix_test_file(tf):
            print(f"  [FIXED] {tf.name}")
            fixed += 1

    print(f"\nFixed {fixed}/{len(test_files)} files.")
    print("Common tests should now compile without AMBA includes.")

if __name__ == "__main__":
    main()
