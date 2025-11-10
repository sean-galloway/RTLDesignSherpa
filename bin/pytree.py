# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: pytree
# Purpose: Recursively prints directory structure like the UNIX `tree` command.
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

import argparse
from pathlib import Path


def print_tree(directory, prefix="", exclude_dirs=None, exclude_files=None):
    """Recursively prints directory structure like the UNIX `tree` command.
    Files are displayed first, followed by directories."""
    exclude_dirs = set(exclude_dirs or [])
    exclude_files = set(exclude_files or [])

    # Get all items, filtering out excluded ones
    all_items = [p for p in directory.iterdir() if p.name not in exclude_dirs and p.name not in exclude_files]
    
    # Separate files and directories and sort them independently
    files = sorted([item for item in all_items if item.is_file()])
    directories = sorted([item for item in all_items if item.is_dir()])

    # Display files first
    for index, item in enumerate(files):
        connector = "├── " if index < len(files) - 1 or directories else "└── "
        print(prefix + connector + item.name)

    # Then display directories
    for index, item in enumerate(directories):
        connector = "└── " if index == len(directories) - 1 else "├── "
        print(prefix + connector + item.name)

        # Recursively display subdirectory contents
        extension = "    " if index == len(directories) - 1 else "│   "
        print_tree(item, prefix + extension, exclude_dirs, exclude_files)

def main():
    parser = argparse.ArgumentParser(description="Custom Python Tree Command")
    parser.add_argument("--path", type=str, required=True, help="Root directory to display")
    parser.add_argument("--exclude-dir", type=str, nargs="*", default=[], help="Directories to exclude")
    parser.add_argument("--exclude-file", type=str, nargs="*", default=[], help="Files to exclude")

    args = parser.parse_args()
    root_dir = Path(args.path)
    # DEBUG: Add this line to see what's being captured
    print(f"DEBUG: exclude_dir = {args.exclude_dir}")

    if not root_dir.exists() or not root_dir.is_dir():
        print(f"Error: '{args.path}' is not a valid directory.")
        return

    # print(root_dir.resolve())  # Print root path like `tree` does
    print(root_dir)
    print_tree(root_dir, "", args.exclude_dir, args.exclude_file)

if __name__ == "__main__":
    main()
