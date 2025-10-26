#!/usr/bin/python3.11
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: search_and_replace_directory
# Purpose: Search reursively through a root directory for some specified REGEXs and replace
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""Search reursively through a root directory for some specified REGEXs and replace them with new text"""

import os
import re
import argparse


def search_and_replace(directory, search_pattern, replace_text, file_extensions=None):
    """
    Recursively search and replace text in files within a directory while skipping symbolic links.

    Args:
        directory (str): Root directory to search for files.
        search_pattern (str): Regex pattern to search for.
        replace_text (str): Text to replace the matched pattern with.
        file_extensions (list): List of file extensions to filter (e.g., ['.txt', '.py']). If None, all files are processed.
    """
    for root, _, files in os.walk(directory):
        for file in files:
            filepath = os.path.join(root, file)

            # Skip symbolic links
            if os.path.islink(filepath):
                print(f"Skipping symbolic link: {filepath}")
                continue

            # Skip files that don't match the specified extensions
            if file_extensions and not file.endswith(tuple(file_extensions)):
                continue

            with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
                content = f.read()

            # Perform search and replace
            updated_content = re.sub(search_pattern, replace_text, content)

            # If content was updated, overwrite the file
            if content != updated_content:
                with open(filepath, 'w', encoding='utf-8') as f:
                    f.write(updated_content)
                print(f"Updated: {filepath}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Recursively search and replace text in files.")
    parser.add_argument("directory", help="Root directory to search for files.")
    parser.add_argument("search_pattern", help="Regex pattern to search for.")
    parser.add_argument("replace_text", help="Text to replace the matched pattern with.")
    parser.add_argument(
        "--file-extensions", nargs="+", default=None,
        help=("Optional list of file extensions to filter "
                "(e.g., .txt .py). If not provided, all files are processed.")
    )
    args = parser.parse_args()

    search_and_replace(args.directory, args.search_pattern, args.replace_text, args.file_extensions)
