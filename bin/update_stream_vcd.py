#!/usr/bin/env python3
"""
Add VCD waveform support to STREAM test files.

This script updates STREAM test files to add compile_args, sim_args, and plusargs
with trace flags for VCD waveform generation, matching the AMBA test pattern.

Usage:
    python3 bin/update_stream_vcd.py --dry-run   # Preview changes
    python3 bin/update_stream_vcd.py              # Apply changes

Author: RTL Design Sherpa Project
Created: 2025-10-27
"""

import os
import sys
import re
import argparse
from pathlib import Path


def find_stream_test_files(root_dir):
    """Find all test files in projects/components/stream/dv/tests/"""
    test_files = []
    stream_tests_dir = os.path.join(root_dir, 'projects/components/stream/dv/tests')

    if os.path.exists(stream_tests_dir):
        for root, dirs, files in os.walk(stream_tests_dir):
            for file in files:
                if file.startswith('test_') and file.endswith('.py'):
                    test_files.append(os.path.join(root, file))

    return sorted(test_files)


def update_compile_args(content, filepath):
    """Update compile_args to add trace flags."""
    lines = content.split('\n')
    new_lines = []
    updated = False

    for i, line in enumerate(lines):
        # Look for: compile_args=["-Wno-TIMESCALEMOD"],
        if re.search(r'compile_args\s*=\s*\[.*-Wno-TIMESCALEMOD.*\],?\s*$', line):
            indent = len(line) - len(line.lstrip())
            base_indent = ' ' * indent

            # Add VCD comment header before compile_args
            new_lines.append('')
            new_lines.append(base_indent + '# VCD waveform generation support via WAVES environment variable')
            new_lines.append(base_indent + '# Trace compilation always enabled (minimal overhead)')
            new_lines.append(base_indent + '# Set WAVES=1 to enable VCD dumping for debugging')

            # Replace with full compile_args
            new_lines.append(base_indent + 'compile_args = [')
            new_lines.append(base_indent + '    "--trace",')
            new_lines.append(base_indent + '    "--trace-structs",')
            new_lines.append(base_indent + '    "--trace-depth", "99",')
            new_lines.append(base_indent + '    "-Wno-TIMESCALEMOD",')
            new_lines.append(base_indent + ']')

            updated = True
        # Look for: sim_args=[],
        elif re.search(r'sim_args\s*=\s*\[\s*\],?\s*$', line):
            indent = len(line) - len(line.lstrip())
            base_indent = ' ' * indent

            new_lines.append(base_indent + 'sim_args = [')
            new_lines.append(base_indent + '    "--trace",')
            new_lines.append(base_indent + '    "--trace-structs",')
            new_lines.append(base_indent + '    "--trace-depth", "99",')
            new_lines.append(base_indent + ']')

            updated = True
        # Look for: plusargs=[],
        elif re.search(r'plusargs\s*=\s*\[\s*\],?\s*$', line):
            indent = len(line) - len(line.lstrip())
            base_indent = ' ' * indent

            new_lines.append(base_indent + 'plusargs = [')
            new_lines.append(base_indent + '    "--trace",')
            new_lines.append(base_indent + ']')

            updated = True
        else:
            new_lines.append(line)

    return '\n'.join(new_lines), updated


def process_file(filepath, dry_run=False):
    """Process a single test file."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()

        # Check if already has trace flags
        if '--trace' in content and 'compile_args' in content:
            return 'skip', 'Already has VCD trace support'

        # Check if has compile_args to update
        if 'compile_args' not in content:
            return 'skip', 'No compile_args found'

        # Update the file
        new_content, updated = update_compile_args(content, filepath)

        if not updated:
            return 'skip', 'No changes needed'

        if dry_run:
            return 'would_update', 'Would add VCD trace support'
        else:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(new_content)
            return 'updated', 'Added VCD trace support'

    except Exception as e:
        return 'error', str(e)


def main():
    parser = argparse.ArgumentParser(
        description='Add VCD trace support to STREAM test files'
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

    print(f"{'DRY RUN: ' if args.dry_run else ''}Adding VCD trace support to STREAM test files...")
    print(f"Root directory: {args.root}\n")

    # Find all test files
    test_files = find_stream_test_files(args.root)
    print(f"Found {len(test_files)} STREAM test files\n")

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
