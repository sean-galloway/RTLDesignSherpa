# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: casefix
# Purpose: Reads a SystemVerilog file and converts 'case' to 'casez', ignoring comments.
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

import re
import os

def convert_case_to_casez(file_path):
    """Reads a SystemVerilog file and converts 'case' to 'casez', ignoring comments."""
    with open(file_path, 'r') as f:
        lines = f.readlines()

    modified_lines = []
    in_comment = False  # Track multi-line comments

    for line in lines:
        stripped_line = line.strip()

        # Handle multi-line comments
        if "/*" in stripped_line:
            in_comment = True
        if "*/" in stripped_line:
            in_comment = False
            modified_lines.append(line)
            continue

        # Ignore single-line comments
        if stripped_line.startswith("//") or in_comment:
            modified_lines.append(line)
            continue

        # Convert `case` to `casez`, ensuring it's a standalone keyword
        line = re.sub(r'\bcase\b', 'casez', line)

        modified_lines.append(line)

    # Overwrite the original file with changes
    with open(file_path, 'w') as f:
        f.writelines(modified_lines)

    print(f"Updated: {file_path}")

def process_sv_files(directory):
    """Recursively finds and processes all .sv files in the given directory."""
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith(".sv"):
                file_path = os.path.join(root, file)
                convert_case_to_casez(file_path)

# Example usage
dir_path = "./rtl"  # Change this to your target directory
process_sv_files(dir_path)

