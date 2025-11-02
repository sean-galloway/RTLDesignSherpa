#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: remove_file_headers
# Purpose: Remove SPDX headers from files for regeneration.
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""
Remove SPDX headers from files for regeneration.

Usage:
    python3 bin/remove_file_headers.py --yes
"""

import os
import sys
import argparse
from pathlib import Path

def remove_header(filepath: Path) -> bool:
    """Remove SPDX header from file."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"Error reading {filepath}: {e}")
        return False

    # Check if file has SPDX header
    if 'SPDX-License-Identifier' not in content[:500]:
        return False  # No header to remove

    lines = content.split('\n')

    # Find where header ends
    # For SystemVerilog: lines start with '//'
    # For Python: lines start with '#'
    header_end = 0
    in_header = False

    if filepath.suffix in ['.sv', '.svh']:
        comment_char = '//'
    elif filepath.suffix == '.py':
        comment_char = '#'
        # Skip shebang if present
        if lines and lines[0].startswith('#!'):
            header_end = 1
    else:
        return False

    # Find end of header block
    for i in range(header_end, len(lines)):
        line = lines[i].strip()
        if line.startswith(comment_char) or line == '':
            if 'SPDX' in line or 'Copyright' in line or 'RTL Design Sherpa' in line or \
               'Module:' in line or 'Purpose:' in line or 'Documentation:' in line or \
               'Subsystem:' in line or 'Author:' in line or 'Created:' in line or \
               'https://github.com' in line:
                in_header = True
                continue
            elif in_header and line.startswith(comment_char):
                continue  # Still in comment block
            elif in_header and line == '':
                continue  # Empty line after header
        else:
            # Found non-comment, non-empty line
            if in_header:
                header_end = i
                break

    # Reconstruct file without header
    if filepath.suffix == '.py' and lines and lines[0].startswith('#!'):
        # Preserve shebang
        new_content = lines[0] + '\n' + '\n'.join(lines[header_end:])
    else:
        new_content = '\n'.join(lines[header_end:])

    # Remove leading blank lines
    new_content = new_content.lstrip('\n')

    try:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(new_content)
        return True
    except Exception as e:
        print(f"Error writing {filepath}: {e}")
        return False

def main():
    parser = argparse.ArgumentParser(description='Remove SPDX headers from files')
    parser.add_argument('--yes', '-y', action='store_true', help='Skip confirmation')
    args = parser.parse_args()

    if not args.yes:
        response = input("This will remove all SPDX headers. Continue? [y/N]: ")
        if response.lower() != 'y':
            print("Aborted")
            return 0

    script_dir = Path(__file__).parent.absolute()
    repo_root = script_dir.parent

    count = 0
    for ext in ['.sv', '.svh', '.py']:
        for filepath in repo_root.rglob(f'*{ext}'):
            # Skip certain directories
            if any(skip in str(filepath) for skip in ['.git', '__pycache__', 'build', 'sim_build', 'venv', 'node_modules']):
                continue

            # Skip symlinks
            if filepath.is_symlink():
                continue

            # Skip conftest.py and __init__.py
            if filepath.name in ['conftest.py', '__init__.py']:
                continue

            if remove_header(filepath):
                count += 1
                if count % 100 == 0:
                    print(f"Processed {count} files...")

    print(f"\nRemoved headers from {count} files")
    return 0

if __name__ == '__main__':
    sys.exit(main())
