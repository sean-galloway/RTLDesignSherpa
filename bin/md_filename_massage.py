#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: md_filename_massage
# Purpose: File Renamer Script - Adds directory path prefixes to filenames
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""
File Renamer Script - Adds directory path prefixes to filenames

This script recursively traverses a directory tree and renames files by prefixing
them with their directory path structure, using underscores as separators.

Usage:
    python rename_files_with_path.py [root_directory] [--dry-run] [--file-extensions ext1,ext2]

Examples:
    python rename_files_with_path.py CocoTBFramework
    python rename_files_with_path.py CocoTBFramework --dry-run
    python rename_files_with_path.py CocoTBFramework --file-extensions md,txt
"""

import os
import sys
import argparse
from pathlib import Path
from typing import List, Set, Tuple


def should_rename_file(filename: str, file_extensions: Set[str]) -> bool:
    """
    Determine if a file should be renamed based on its extension.

    Args:
        filename: The filename to check
        file_extensions: Set of allowed file extensions (without dots)

    Returns:
        True if the file should be renamed, False otherwise
    """
    if not file_extensions:
        return True  # No filter specified, rename all files

    file_ext = Path(filename).suffix.lstrip('.')
    return file_ext.lower() in file_extensions


def generate_new_filename(file_path: Path, root_path: Path) -> str:
    """
    Generate the new filename with directory path prefix.

    Args:
        file_path: Path to the file
        root_path: Root directory path

    Returns:
        New filename with path prefix
    """
    # Get relative path from root
    relative_path = file_path.relative_to(root_path)

    # Get directory components (excluding the filename)
    dir_parts = relative_path.parent.parts

    # Get the original filename
    original_filename = file_path.name

    # Check if filename already has the directory prefix
    expected_prefix = "_".join(dir_parts) + "_" if dir_parts else ""

    if original_filename.startswith(expected_prefix):
        # Filename already has the correct prefix
        return original_filename

    # Create new filename with directory prefix
    if dir_parts:
        new_filename = "_".join(dir_parts) + "_" + original_filename
    else:
        # File is in root directory, no prefix needed
        new_filename = original_filename

    return new_filename


def find_files_to_rename(root_directory: str, file_extensions: Set[str]) -> List[Tuple[Path, str]]:
    """
    Find all files that need to be renamed.

    Args:
        root_directory: Root directory to search
        file_extensions: Set of allowed file extensions

    Returns:
        List of tuples containing (current_path, new_filename)
    """
    root_path = Path(root_directory).resolve()
    files_to_rename = []

    # Walk through all files recursively
    for file_path in root_path.rglob('*'):
        if file_path.is_file() and should_rename_file(file_path.name, file_extensions):
            new_filename = generate_new_filename(file_path, root_path)

            # Only add to list if the filename will actually change
            if new_filename != file_path.name:
                files_to_rename.append((file_path, new_filename))

    return files_to_rename


def rename_files(files_to_rename: List[Tuple[Path, str]], dry_run: bool = False) -> None:
    """
    Rename the files.

    Args:
        files_to_rename: List of tuples containing (current_path, new_filename)
        dry_run: If True, only print what would be done without actually renaming
    """
    if not files_to_rename:
        print("No files need to be renamed.")
        return

    print(f"{'DRY RUN - ' if dry_run else ''}Found {len(files_to_rename)} files to rename:")
    print()

    for current_path, new_filename in files_to_rename:
        new_path = current_path.parent / new_filename

        # Display the operation
        relative_current = current_path.relative_to(Path.cwd()) if current_path.is_relative_to(Path.cwd()) else current_path
        relative_new = new_path.relative_to(Path.cwd()) if new_path.is_relative_to(Path.cwd()) else new_path

        print(f"  {relative_current}")
        print(f"  -> {relative_new}")
        print()

        if not dry_run:
            try:
                # Check if target file already exists
                if new_path.exists():
                    print(f"    WARNING: Target file already exists, skipping: {new_path}")
                    continue

                # Perform the rename
                current_path.rename(new_path)
                print(f"    ✓ Successfully renamed")
            except Exception as e:
                print(f"    ✗ Error renaming file: {e}")
        else:
            print(f"    (Would rename)")

        print()


def parse_file_extensions(extensions_str: str) -> Set[str]:
    """
    Parse comma-separated file extensions string.

    Args:
        extensions_str: Comma-separated string of file extensions

    Returns:
        Set of lowercase file extensions without dots
    """
    if not extensions_str:
        return set()

    extensions = set()
    for ext in extensions_str.split(','):
        ext = ext.strip().lstrip('.').lower()
        if ext:
            extensions.add(ext)

    return extensions


def main():
    """Main function to handle command line arguments and execute the renaming."""
    parser = argparse.ArgumentParser(
        description="Rename files by adding directory path prefixes",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s CocoTBFramework
  %(prog)s CocoTBFramework --dry-run
  %(prog)s CocoTBFramework --file-extensions md,txt
  %(prog)s /path/to/directory --dry-run --file-extensions md
        """
    )

    parser.add_argument(
        'root_directory',
        nargs='?',
        default='.',
        help='Root directory to process (default: current directory)'
    )

    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='Show what would be renamed without actually renaming files'
    )

    parser.add_argument(
        '--file-extensions',
        type=str,
        default='',
        help='Comma-separated list of file extensions to process (e.g., "md,txt,py"). If not specified, all files are processed.'
    )

    args = parser.parse_args()

    # Validate root directory
    root_path = Path(args.root_directory)
    if not root_path.exists():
        print(f"Error: Directory '{args.root_directory}' does not exist.")
        sys.exit(1)

    if not root_path.is_dir():
        print(f"Error: '{args.root_directory}' is not a directory.")
        sys.exit(1)

    # Parse file extensions
    file_extensions = parse_file_extensions(args.file_extensions)

    # Display configuration
    print(f"Processing directory: {root_path.resolve()}")
    if file_extensions:
        print(f"File extensions filter: {', '.join(sorted(file_extensions))}")
    else:
        print("File extensions filter: All files")
    print(f"Mode: {'Dry run' if args.dry_run else 'Live execution'}")
    print()

    # Find files to rename
    try:
        files_to_rename = find_files_to_rename(str(root_path), file_extensions)
    except Exception as e:
        print(f"Error finding files: {e}")
        sys.exit(1)

    # Rename files
    try:
        rename_files(files_to_rename, args.dry_run)
    except Exception as e:
        print(f"Error during renaming: {e}")
        sys.exit(1)

    if files_to_rename and not args.dry_run:
        print(f"Successfully processed {len(files_to_rename)} files.")
    elif args.dry_run and files_to_rename:
        print(f"Dry run complete. {len(files_to_rename)} files would be renamed.")
        print("Run without --dry-run to perform the actual renaming.")


if __name__ == '__main__':
    main()
