# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: filelist_utils
# Purpose: Utility functions for processing RTL file lists in CocoTB tests.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Utility functions for processing RTL file lists in CocoTB tests.

This module provides helper functions to integrate the FileListProcessor
with CocoTB test runners, making it easy to use hierarchical .f file lists
instead of manually specifying verilog_sources in every test.

Usage Example:
    from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

    def test_scheduler(request, ...):
        module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

        # Get sources from file list (replaces manual verilog_sources list)
        verilog_sources, includes = get_sources_from_filelist(
            repo_root=repo_root,
            filelist_path='rtl/rapids/filelists/fub/scheduler.f'
        )

        run(
            verilog_sources=verilog_sources,
            includes=includes,
            ...
        )
"""

import os
import sys
from pathlib import Path


def get_sources_from_filelist(repo_root, filelist_path):
    """
    Process an RTL file list and return verilog_sources and includes for CocoTB.

    Args:
        repo_root (str): Absolute path to repository root
        filelist_path (str): Relative path from repo_root to .f file
                             Example: 'rtl/rapids/filelists/fub/scheduler.f'

    Returns:
        tuple: (verilog_sources, includes)
            - verilog_sources: List of absolute paths to Verilog files
            - includes: List of absolute paths to include directories

    Example:
        verilog_sources, includes = get_sources_from_filelist(
            repo_root='/path/to/rtldesignsherpa',
            filelist_path='rtl/rapids/filelists/fub/scheduler.f'
        )

    File List Format:
        # Comments start with # or //
        +incdir+$REPO_ROOT/rtl/rapids/includes     # Include directory
        -f $REPO_ROOT/path/to/other.f            # Include another file list
        $REPO_ROOT/rtl/rapids/rapids_fub/module.sv   # Verilog source file

    Note:
        - Sets REPO_ROOT environment variable for file list processor
        - Automatically resolves -f directives (hierarchical inclusion)
        - Removes duplicates from final lists
    """
    # Import FileListProcessor (add to path if needed)
    filelist_processor_dir = Path(repo_root) / 'bin' / 'FileFolderFunctions'
    if str(filelist_processor_dir) not in sys.path:
        sys.path.insert(0, str(filelist_processor_dir))

    from file_list_processor import FileListProcessor

    # Set REPO_ROOT environment variable for substitution
    os.environ['REPO_ROOT'] = repo_root

    # Construct absolute path to file list
    filelist_abs = os.path.join(repo_root, filelist_path)

    if not os.path.exists(filelist_abs):
        raise FileNotFoundError(
            f"File list not found: {filelist_abs}\n"
            f"  repo_root: {repo_root}\n"
            f"  filelist_path: {filelist_path}"
        )

    # Process file list
    processor = FileListProcessor([filelist_abs], debug=False)

    # Get resolved lists
    verilog_sources = processor.get_file_list()
    includes_raw = processor.get_include_list()

    # Expand environment variables in includes (FileListProcessor doesn't do this for +incdir+)
    includes = []
    for inc in includes_raw:
        # Replace $VARNAME with environment variable value
        import re
        expanded = re.sub(r'\$(\w+)', lambda m: os.getenv(m.group(1), m.group(0)), inc)
        includes.append(expanded)

    return verilog_sources, includes


def get_sources_from_multiple_filelists(repo_root, filelist_paths):
    """
    Process multiple RTL file lists and merge results.

    Useful when a test needs files from multiple independent file lists
    that aren't hierarchically related via -f directives.

    Args:
        repo_root (str): Absolute path to repository root
        filelist_paths (list): List of relative paths to .f files

    Returns:
        tuple: (verilog_sources, includes) - merged and deduplicated

    Example:
        verilog_sources, includes = get_sources_from_multiple_filelists(
            repo_root='/path/to/rtldesignsherpa',
            filelist_paths=[
                'rtl/rapids/filelists/fub/scheduler.f',
                'rtl/common/filelists/utilities.f'
            ]
        )
    """
    # Import FileListProcessor
    filelist_processor_dir = Path(repo_root) / 'bin' / 'FileFolderFunctions'
    if str(filelist_processor_dir) not in sys.path:
        sys.path.insert(0, str(filelist_processor_dir))

    from file_list_processor import FileListProcessor, remove_dups_from_list

    # Set REPO_ROOT environment variable
    os.environ['REPO_ROOT'] = repo_root

    # Construct absolute paths
    filelist_abs_paths = [os.path.join(repo_root, fp) for fp in filelist_paths]

    # Check all exist
    for filelist_abs in filelist_abs_paths:
        if not os.path.exists(filelist_abs):
            raise FileNotFoundError(f"File list not found: {filelist_abs}")

    # Process all file lists
    processor = FileListProcessor(filelist_abs_paths, debug=False)

    # Get merged, deduplicated lists
    verilog_sources = processor.get_file_list()
    includes = processor.get_include_list()

    return verilog_sources, includes


def debug_filelist(repo_root, filelist_path, output_file='filelist_debug.txt'):
    """
    Debug helper: Process file list and write detailed debug output.

    Args:
        repo_root (str): Absolute path to repository root
        filelist_path (str): Relative path to .f file
        output_file (str): Where to write debug output

    Returns:
        tuple: (verilog_sources, includes)

    Side Effects:
        Writes debug information to output_file showing:
        - All processed files
        - Hierarchy of -f inclusions
        - Final deduplicated lists

    Example:
        verilog_sources, includes = debug_filelist(
            repo_root='/path/to/rtldesignsherpa',
            filelist_path='rtl/rapids/filelists/macro/scheduler_group.f',
            output_file='scheduler_group_debug.txt'
        )
        # Check scheduler_group_debug.txt for processing details
    """
    # Import FileListProcessor
    filelist_processor_dir = Path(repo_root) / 'bin' / 'FileFolderFunctions'
    if str(filelist_processor_dir) not in sys.path:
        sys.path.insert(0, str(filelist_processor_dir))

    from file_list_processor import FileListProcessor

    # Set REPO_ROOT environment variable
    os.environ['REPO_ROOT'] = repo_root

    # Construct absolute path
    filelist_abs = os.path.join(repo_root, filelist_path)

    if not os.path.exists(filelist_abs):
        raise FileNotFoundError(f"File list not found: {filelist_abs}")

    # Process with debug enabled
    processor = FileListProcessor([filelist_abs], debug=True)

    # Get results
    verilog_sources = processor.get_file_list()
    includes = processor.get_include_list()

    print(f"✓ Debug output written to: {output_file}")
    print(f"  Verilog sources: {len(verilog_sources)} files")
    print(f"  Include dirs: {len(includes)} directories")

    return verilog_sources, includes
