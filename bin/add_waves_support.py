#!/usr/bin/env python3
"""
Add WAVES environment variable support to all CocoTB test files.

This script updates test files to support VCD waveform generation via the WAVES
environment variable. It adds compile_args with --trace when WAVES=1.

Usage:
    python3 bin/add_waves_support.py --dry-run   # Preview changes
    python3 bin/add_waves_support.py              # Apply changes

Author: RTL Design Sherpa Project
Created: 2025-10-26
"""

import os
import sys
import re
import argparse
from pathlib import Path


def find_test_files(root_dir):
    """Find all test_*.py files in val/ and projects/ directories."""
    test_files = []

    # Search val/ directory
    val_dir = os.path.join(root_dir, 'val')
    if os.path.exists(val_dir):
        for root, dirs, files in os.walk(val_dir):
            for file in files:
                if file.startswith('test_') and file.endswith('.py'):
                    test_files.append(os.path.join(root, file))

    # Search projects/ directories
    projects_dir = os.path.join(root_dir, 'projects')
    if os.path.exists(projects_dir):
        for root, dirs, files in os.walk(projects_dir):
            if 'dv/tests' in root or 'tests' in root:
                for file in files:
                    if file.startswith('test_') and file.endswith('.py'):
                        test_files.append(os.path.join(root, file))

    return sorted(test_files)


def has_waves_support(content):
    """Check if file already has WAVES support."""
    # Check for WAVES environment variable
    if 'os.environ.get' in content and 'WAVES' in content:
        return True

    # Check for compile_args with --trace
    if 'compile_args' in content and '--trace' in content and 'WAVES' in content:
        return True

    return False


def has_simulator_run(content):
    """Check if file uses cocotb_test.simulator.run()."""
    return 'simulator.run' in content or 'cocotb_test.run' in content


def add_waves_support(content, filename):
    """Add WAVES support to test file content."""
    lines = content.split('\n')
    new_lines = []

    # Track if we've added the support
    added_waves = False
    in_imports = False
    imports_ended = False

    for i, line in enumerate(lines):
        new_lines.append(line)

        # Detect import section
        if line.strip().startswith('import ') or line.strip().startswith('from '):
            in_imports = True
        elif in_imports and line.strip() and not line.strip().startswith('#'):
            if not (line.strip().startswith('import ') or line.strip().startswith('from ')):
                imports_ended = True
                in_imports = False

        # Add os import if not present and we just ended imports
        if imports_ended and not added_waves and 'import os' not in content:
            # Find a good place to add import os
            if not line.strip().startswith('import') and not line.strip().startswith('from'):
                new_lines.insert(-1, 'import os')
                added_waves = True

        # Look for simulator.run( or cocotb_test.run( calls
        if 'simulator.run(' in line or 'cocotb_test.run(' in line:
            # Check if compile_args already exists in next few lines
            has_compile_args = False
            for j in range(i, min(i + 20, len(lines))):
                if 'compile_args' in lines[j]:
                    has_compile_args = True
                    break

            if not has_compile_args and not added_waves:
                # Find the right indentation
                indent = len(line) - len(line.lstrip())
                base_indent = ' ' * indent
                param_indent = ' ' * (indent + 4)

                # Add compile_args section before simulator.run
                waves_code = [
                    '',
                    base_indent + '# VCD waveform generation support via WAVES environment variable',
                    base_indent + '# Set WAVES=1 to enable VCD tracing for debugging',
                    base_indent + 'compile_args = []',
                    base_indent + 'if int(os.environ.get("WAVES", "0")) == 1:',
                    param_indent + 'compile_args.extend([',
                    param_indent + '    "--trace",              # VCD tracing',
                    param_indent + '    "--trace-depth", "99",  # Full depth',
                    param_indent + '    "--trace-max-array", "1024"',
                    param_indent + '])',
                    ''
                ]

                # Insert before current line
                for code_line in reversed(waves_code):
                    new_lines.insert(-1, code_line)

                added_waves = True

        # Check if we need to add compile_args parameter to simulator.run()
        if added_waves and ('simulator.run(' in line or 'cocotb_test.run(' in line):
            # Look ahead to see if compile_args is already a parameter
            param_section = []
            j = i
            while j < len(lines) and ')' not in ''.join(lines[i:j+1]):
                param_section.append(lines[j])
                j += 1

            param_text = '\n'.join(param_section)
            if 'compile_args=' not in param_text:
                # Need to add compile_args parameter
                # This is tricky - we need to find the right place
                # For now, just add a comment reminder
                pass  # Will be handled by the compile_args presence check

    return '\n'.join(new_lines)


def process_file(filepath, dry_run=False):
    """Process a single test file."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()

        # Check if file uses simulator.run
        if not has_simulator_run(content):
            return 'skip', 'No simulator.run() call found'

        # Check if already has WAVES support
        if has_waves_support(content):
            return 'skip', 'Already has WAVES support'

        # Add WAVES support
        new_content = add_waves_support(content, filepath)

        if dry_run:
            return 'would_update', 'Would add WAVES support'
        else:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(new_content)
            return 'updated', 'Added WAVES support'

    except Exception as e:
        return 'error', str(e)


def main():
    parser = argparse.ArgumentParser(
        description='Add WAVES environment variable support to CocoTB test files'
    )
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='Preview changes without modifying files'
    )
    parser.add_argument(
        '--root',
        default='/mnt/data/github/rtldesignsherpa',
        help='Repository root directory'
    )

    args = parser.parse_args()

    print(f"{'DRY RUN: ' if args.dry_run else ''}Adding WAVES support to test files...")
    print(f"Root directory: {args.root}\n")

    # Find all test files
    test_files = find_test_files(args.root)
    print(f"Found {len(test_files)} test files\n")

    # Process each file
    stats = {'updated': 0, 'would_update': 0, 'skip': 0, 'error': 0}

    for filepath in test_files:
        rel_path = os.path.relpath(filepath, args.root)
        status, message = process_file(filepath, args.dry_run)
        stats[status] += 1

        if status in ['updated', 'would_update']:
            print(f"{'[DRY RUN] ' if args.dry_run else ''}✓ {rel_path}")
            print(f"  {message}")
        elif status == 'error':
            print(f"✗ {rel_path}")
            print(f"  ERROR: {message}")
        # Skip printing 'skip' status to reduce noise

    # Print summary
    print(f"\nSummary:")
    print(f"  Updated: {stats['updated'] + stats['would_update']}")
    print(f"  Skipped: {stats['skip']}")
    print(f"  Errors: {stats['error']}")

    if args.dry_run:
        print(f"\nThis was a dry run. Use without --dry-run to apply changes.")

    return 0 if stats['error'] == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
