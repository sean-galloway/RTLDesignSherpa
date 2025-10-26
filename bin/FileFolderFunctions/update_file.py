# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: UpdateFile
# Purpose: Updates selected text in files
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""Updates selected text in files"""

import os
import re
import subprocess
import chardet


def convert_to_utf8(input_file, output_file=None):
    """
    Converts a file with any encoding into UTF-8.
    
    Args:
        input_file (str): Path to the input file.
        output_file (str, optional): Path to save the UTF-8 encoded output file. If None, the function returns the content as a UTF-8 list of lines.
    
    Returns:
        list: UTF-8 encoded lines if `output_file` is None.
    """
    # Check for zero-length file
    if os.path.getsize(input_file) == 0:
        print(f"Skipping '{input_file}': File is empty (zero length).")
        return None if output_file else []

    print(f'convert_to_utf8: {input_file}')
    # Detect the file's encoding
    with open(input_file, "rb") as f:
        raw_data = f.read()
        result = chardet.detect(raw_data)  # Detect encoding
        source_encoding = result["encoding"]
        confidence = result["confidence"]

        if not source_encoding:
            print(f"Error: Could not detect the file's encoding. {input_file}")

        print(f"Detected Encoding: {source_encoding} (Confidence: {confidence * 100:.2f}%)")

    # Decode the file's content using the detected encoding
    with open(input_file, "r", encoding=source_encoding, errors="replace") as f:
        content = f.readlines()  # Read and decode the file as a list of lines

    # If an output file is specified, write the content as UTF-8
    if output_file:
        with open(output_file, "w", encoding="utf-8") as f:
            f.writelines(content)
        print(f"File successfully converted to UTF-8 and saved as '{output_file}'")
        return None

    # Otherwise, return the UTF-8 encoded content as lines
    return content


class UpdateFile:
    """Manages file updates across a repository using regex substitutions.

    The UpdateFile class provides methods to find, report, and apply text
        substitutions across multiple files in a repository. It supports
        searching and replacing text patterns in various file types.

    Attributes:
        repo_root (str): Root directory of the git repository.
        root_dir (str): Specific directory to start searching from.
        regex_list (list): List of regex search and replace patterns.
        subs_data (dict): Stores file substitution details.
    """
    def __init__(self, root_dir, regex_list, skip_regex_list=None):
        """
        Initializes the UpdateFile class.

        Args:
            root_dir (str): Root directory to start searching from (relative to the repo root).
            regex_list (list): List of [search, replace] regex pairs.
            skip_regex_list (list, optional): List of regex patterns. Lines matching these patterns will be skipped.
        """
        # Determine the repository root
        self.repo_root = subprocess.check_output(
            ['git', 'rev-parse', '--show-toplevel']
        ).strip().decode('utf-8')

        # Root directory to search, relative to the repository root
        self.root_dir = os.path.join(self.repo_root, root_dir)
        self.regex_list = regex_list  # List of [search, replace] regex pairs
        self.skip_regex_list = skip_regex_list or []  # List of regex patterns to skip

        # Data structure to store substitutions: {filename: [(line_num, before, after), ...]}
        self.subs_data = {}


    def find_items(self):
        """
        Finds all files containing lines that match the search patterns, performs in-memory substitutions,
        and stores the results in self.subs_data.

        Each entry in self.subs_data contains:
        - File name
        - Line number
        - Original line (before substitution)
        - Updated line (after applying all substitutions)
        """
        text_files = (
            '.v', '.sv', '.vhd', 'Makefile', '.tcl', '.f', '.h', '.sh', '.py', '.prj',
            '.sgdc', '.sdc', '.awl', '.do', '.xml', '.gitignore', '.lst', 'readme',
            '.txt', '_cmd', '_syn', 'clean_up', '.scandef', '.tcd', '.rpt'
        )
        if not os.path.exists(self.root_dir):
            raise FileNotFoundError(f"Root directory '{self.root_dir}' does not exist.")

        # Walk through all files in the root directory recursively
        for root, _, files in os.walk(self.root_dir):
            for filename in files:
                file_path = os.path.join(root, filename)
                rel_file_path = os.path.relpath(file_path, self.repo_root)

                # Skip non-text files (optional)
                if not filename.endswith(text_files):
                    continue

                # Process the file
                lines = convert_to_utf8(file_path)
                if not lines:
                    continue

                # Track changes for this file
                changes = []

                # Check each line for matches
                for i, line in enumerate(lines):
                    # Skip the line if it matches any of the skip_regex patterns
                    if any(re.search(skip_pattern, line) for skip_pattern in self.skip_regex_list):
                        continue

                    updated_line = line
                    for search, replace in self.regex_list:
                        # Apply substitutions
                        if re.search(search, updated_line):
                            updated_line = re.sub(search, replace, updated_line)

                    # If the line changed, store the before/after
                    if updated_line != line:
                        changes.append((i + 1, line.rstrip(), updated_line.rstrip()))  # Line numbers are 1-based

                # Save changes if any substitutions were found
                if changes:
                    self.subs_data[rel_file_path] = changes


    def report_items(self, filename):
        """
        Reports all substitutions found and stored in self.subs_data.
        Args:
            filename (str): Name of the output file.
        """
        if not self.subs_data:
            print("report_items: No substitutions found. Did you run find_items()?") 
            return

        print(f'report_items: {len(self.subs_data)} files to substitute')

        with open(filename, 'w') as f:
            f.write("\nSubstitution Report\n")
            f.write("=" * 80 + '\n')
            for file, changes in self.subs_data.items():
                f.write(f"File: {file}\n")
                f.write("-" * 80 + '\n')
                for line_num, before, after in changes:
                    f.write(f"Line {line_num}:\n")
                    f.write(f"  Before: {before}\n")
                    f.write(f"  After : {after}\n")
                    f.write("-" * 80 + '\n')
        print(f"Report written to {filename}")


    def sub_items(self):
        """
        Applies the substitutions to the actual files in place.
        """
        if not self.subs_data:
            print("sub_items: No substitutions to apply. Did you run find_items()?") 
            return

        print("\nApplying Substitutions...")
        for rel_file_path, changes in self.subs_data.items():
            file_path = os.path.join(self.repo_root, rel_file_path)

            # Read the original file
            lines = convert_to_utf8(file_path)
            if not lines:
                continue

            # Apply the changes
            for line_num, _, updated_line in changes:
                lines[line_num - 1] = f"{updated_line}\n"  # Correctly append a newline character

            # Write back the updated content
            with open(file_path, 'w') as file:
                file.writelines(lines)

            print(f"Updated File: {rel_file_path}")
        print("\nAll substitutions applied successfully.")
