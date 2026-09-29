# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: filelist_utils
# Purpose: Utility functions for processing RTL file lists in CocoTB tests.
#
# Documentation: cocotb-framework PyPI package
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
    from TBClasses.shared.filelist_utils import get_sources_from_filelist

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


def _registry_filelist_dirs(repo_root):
    """Every filelist directory bin/filelists.toml registers, as absolute Paths."""
    import tomllib
    reg = Path(repo_root) / 'bin' / 'filelists.toml'
    if not reg.is_file():
        raise FileNotFoundError(f"filelist registry not found: {reg}")
    data = tomllib.loads(reg.read_text())
    dirs = []
    for area in data.get('area', []):
        for d in area.get('filelist_dirs', []):
            dirs.append(Path(repo_root) / d)
    return dirs


def _direct_sources(filelist, repo_root):
    """Source files a .f names DIRECTLY (not through -f), as absolute Paths."""
    out = []
    for raw in Path(filelist).read_text(errors='ignore').splitlines():
        line = raw.split('#', 1)[0].split('//', 1)[0].strip()
        if not line or line.startswith(('-f', '+incdir+', '-')):
            continue
        out.append(Path(line.replace('$REPO_ROOT', str(repo_root))
                            .replace('${REPO_ROOT}', str(repo_root))))
    return out


def filelist_for(repo_root, module):
    """The repo-relative .f that provides `module`, resolved through the registry.

    tooling TASK-005 (was TOOL-011): tests used to hardcode
    filelist_path='rtl/common/filelists/fifo_async.f', so moving a module's .f
    (the CDC reorg moved twelve) meant editing every test that named the old
    path -- and a missed one resolved to nothing and the test "passed" against
    no DUT. A test now names the MODULE; where its filelist lives is the
    registry's concern.

    Resolution, cheapest first:
      1. a filelist named exactly `<module>.f` under a registered filelist dir
         (the repo convention: one filelist per module, named after it);
      2. otherwise every registered .f whose DIRECT sources include
         `<module>.sv`.
    Exactly one answer is required. None raises FileNotFoundError, several
    raise ValueError naming them -- never a silent guess, because a wrong
    filelist is the failure this exists to remove.
    """
    repo_root = Path(repo_root)
    dirs = _registry_filelist_dirs(repo_root)
    named = sorted({p for d in dirs if d.is_dir() for p in d.rglob(f'{module}.f')})
    if len(named) == 1:
        return str(named[0].relative_to(repo_root))
    if len(named) > 1:
        raise ValueError(f"filelist_for({module!r}): {len(named)} filelists named {module}.f: "
                         + ', '.join(str(p.relative_to(repo_root)) for p in named))
    providers = []
    for d in dirs:
        if not d.is_dir():
            continue
        for fl in sorted(d.rglob('*.f')):
            if any(src.name == f'{module}.sv' for src in _direct_sources(fl, repo_root)):
                providers.append(str(fl.relative_to(repo_root)))
    if len(providers) == 1:
        return providers[0]
    if not providers:
        raise FileNotFoundError(f"filelist_for({module!r}): no registered filelist is named "
                                f"{module}.f or lists {module}.sv directly (bin/filelists.toml)")
    raise ValueError(f"filelist_for({module!r}): {len(providers)} registered filelists list "
                     f"{module}.sv directly: " + ', '.join(providers)
                     + " -- name the one you mean with filelist_path=")


def get_sources_from_filelist(repo_root, filelist_path=None, *, module=None):
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
    if (filelist_path is None) == (module is None):
        raise ValueError("get_sources_from_filelist: pass exactly one of filelist_path= or module=")
    if module is not None:
        filelist_path = filelist_for(repo_root, module)

    # Import FileListProcessor (add to path if needed)
    filelist_processor_dir = Path(repo_root) / 'bin' / 'FileFolderFunctions'
    if str(filelist_processor_dir) not in sys.path:
        sys.path.insert(0, str(filelist_processor_dir))

    from file_list_processor import FileListProcessor

    # Set REPO_ROOT environment variable for substitution
    os.environ['REPO_ROOT'] = repo_root

    # Set the root variables that filelists reference for cross-component
    # dependencies. These mirror env_python; anything defined there and used in
    # a .f must appear here too, or the filelist resolves under `make` (which
    # sources env_python) but breaks for cocotb tests, which do not.
    #
    # This list previously drifted from env_python -- RAPIDS_ROOT and the
    # NexysA7 characterization roots were exported by env_python and used by
    # filelists but were missing here, so those filelists could not be consumed
    # from a test. Existing environment values win, so a flow Makefile can still
    # override any of these.
    components_root = os.path.join(repo_root, 'projects', 'components')
    nexys_root = os.path.join(repo_root, 'projects', 'NexysA7')

    genesys2_stream = os.path.join(repo_root, 'projects', 'fpga-systems', 'Genesys2', 'stream')

    defaults = {
        'APB_XBAR_ROOT': os.path.join(components_root, 'apbx_xbar'),
        'BCH_ROOT': os.path.join(components_root, 'bch'),
        'BRIDGE_ROOT': os.path.join(components_root, 'bridge'),
        'CONVERTERS_ROOT': os.path.join(components_root, 'utility-ip', 'converters'),
        'DELTA_ROOT': os.path.join(components_root, 'noc-ip', 'delta'),
        'MISC_ROOT': os.path.join(components_root, 'utility-ip', 'misc'),
        'RAPIDS_ROOT': os.path.join(components_root, 'dma-ip', 'rapids'),
        'RETRO_ROOT': os.path.join(components_root, 'retro_legacy_blocks'),
        'STREAM_ROOT': os.path.join(components_root, 'dma-ip', 'stream'),
        # Nexys stream_characterization deleted 2026-08-30; both now point at
        # the Genesys 2 flow that absorbed the collateral.
        'STREAM_CHAR_ROOT': genesys2_stream,
        'STREAM_CHAR_FRAMEWORK_ROOT': genesys2_stream,
        'DDR2_CHAR_FRAMEWORK_ROOT': os.path.join(repo_root, 'projects', 'fpga-systems', 'NexysA7', 'pumice', 'ddr2_char_framework'),
        # timing_characterization moved to projects/asic-trials/ in f5a4a50b1;
        # it is an ASIC run, not a Nexys board flow. filelist_registry.py's
        # ROOT_VARS already mapped it there -- this default was missed.
        'TIMING_CHAR_ROOT': os.path.join(repo_root, 'projects', 'asic-trials', 'timing_characterization'),
    }
    for var, value in defaults.items():
        os.environ.setdefault(var, value)

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

    # Get resolved lists (may contain relative paths)
    verilog_sources_raw = processor.get_file_list()
    includes_raw = processor.get_include_list()

    # Get filelist directory for resolving relative paths
    filelist_dir = os.path.dirname(filelist_abs)

    # Bridge convention: paths in filelist are relative to parent of filelist directory
    # Example: filelist at rtl/filelists/bridge_1x2_wr.f, paths relative to rtl/
    base_dir = os.path.dirname(filelist_dir)

    # Resolve verilog_sources relative to base directory (parent of filelist dir)
    verilog_sources = []
    for source in verilog_sources_raw:
        if os.path.isabs(source):
            # Already absolute
            verilog_sources.append(source)
        else:
            # Relative to base directory (parent of filelist directory)
            abs_path = os.path.normpath(os.path.join(base_dir, source))
            verilog_sources.append(abs_path)

    # Resolve include directories relative to base directory (same as verilog_sources)
    includes = []
    for inc in includes_raw:
        # First expand environment variables
        import re
        expanded = re.sub(r'\$(\w+)', lambda m: os.getenv(m.group(1), m.group(0)), inc)

        # Then resolve relative paths
        if os.path.isabs(expanded):
            # Already absolute
            includes.append(expanded)
        else:
            # Relative to base directory (parent of filelist directory)
            abs_path = os.path.normpath(os.path.join(base_dir, expanded))
            includes.append(abs_path)

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

    print(f"Debug output written to: {output_file}")
    print(f"  Verilog sources: {len(verilog_sources)} files")
    print(f"  Include dirs: {len(includes)} directories")

    return verilog_sources, includes
