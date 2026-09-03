# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: utilities
# Purpose: Returns module, repo_root, test_dir (relative to the calling file), log_dir, and
#
# Documentation: cocotb-framework PyPI package
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

'''Various Utilities for the CocoTB Flow'''
import os
import subprocess
import inspect
import logging
import tempfile
import time
from typing import Dict, Tuple, Optional, List


def get_repo_root():
    """Absolute path to the repository root.

    Derived from THIS FILE's location, not from `git rev-parse` in the
    process's cwd. The git form has a hidden cwd dependency: a simulator
    runs with cwd set to its build directory, and the moment that directory
    lives outside the repo (which SIM_BUILD_ROOT allows, and which is the
    whole point of it) `git rev-parse --show-toplevel` exits 128 and every
    caller dies with an empty results file. This module is always at
    <repo>/bin/TBClasses/shared/utilities.py, so walking up is exact,
    cwd-independent, and cheaper than a subprocess.

    REPO_ROOT overrides it for anyone vendoring these classes elsewhere.
    """
    env = os.environ.get('REPO_ROOT')
    if env:
        return env
    return os.path.abspath(
        os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))


# ---------------------------------------------------------------------------
# Simulation build root, and the busy semaphore that protects it.
#
# WHY THIS EXISTS. val/<area>/local_sim_build/ used to be a single shared
# build root. Deleting from it while a run is in flight destroys that run's
# build -- reproduced directly: start a parallel set, rm -rf one glob three
# seconds in, and a test fails with
# "FileNotFoundError: RTL source not found" plus a Verilator make error.
# In a shared worktree with concurrent agent sessions, nobody can tell whose
# build they are deleting, and the victim reads as a flaky test.
# See VAL-XDIST-INTERMITTENT.
#
# Two independent protections, because either alone leaves a hole:
#   SIM_BUILD_ROOT -- give each session its own root, so sessions never
#                     share a collision domain in the first place.
#   .sim_busy      -- a per-directory marker naming the owning session and
#                     pid, so anything cleaning a SHARED root can tell an
#                     in-flight build from an abandoned one.
# ---------------------------------------------------------------------------

SIM_BUSY_MARKER = '.sim_busy'


def sim_session_id() -> str:
    """Identity of the session that owns a build directory.

    Explicit SIM_SESSION_ID wins. Otherwise derive one from SIM_BUILD_ROOT
    (a session that set its own root has already declared itself), and fall
    back to 'shared' for the legacy single-root behaviour.
    """
    sid = os.environ.get('SIM_SESSION_ID')
    if sid:
        return sid
    root = os.environ.get('SIM_BUILD_ROOT')
    if root:
        return os.path.basename(os.path.normpath(root)) or 'shared'
    return 'shared'


def sim_build_root(tests_dir: str) -> str:
    """Root under which this session's Verilator build trees live.

    Unset SIM_BUILD_ROOT keeps the historical <tests_dir>/local_sim_build,
    so nothing changes for anyone who does not opt in.

    When SIM_BUILD_ROOT is set, the per-area structure is PRESERVED beneath
    it (<root>/<area path>/local_sim_build) rather than flattened. Flattening
    would trade a cross-session collision for a cross-area one, since build
    directory names are only unique within an area.
    """
    root = os.environ.get('SIM_BUILD_ROOT')
    if not root:
        return os.path.join(tests_dir, 'local_sim_build')

    tests_dir = os.path.abspath(tests_dir)
    try:
        rel = os.path.relpath(tests_dir, get_repo_root())
        if rel.startswith('..'):          # outside the repo: no useful prefix
            rel = os.path.basename(tests_dir)
    except Exception:
        rel = os.path.basename(tests_dir)
    return os.path.join(os.path.abspath(root), rel, 'local_sim_build')


def sim_build_path(tests_dir: str, name: str, mark_busy: bool = True) -> str:
    """Full build directory for one test, created and marked in use.

    The marker records session, pid and start time. It is advisory: it does
    not lock anything, it just lets a cleaner distinguish "another session is
    building here right now" from "leftover from a run that ended", which is
    the distinction that was missing when this bit us.
    """
    path = os.path.join(sim_build_root(tests_dir), name)
    os.makedirs(path, exist_ok=True)
    if mark_busy:
        try:
            with open(os.path.join(path, SIM_BUSY_MARKER), 'w') as fh:
                fh.write(f"session={sim_session_id()}\n"
                         f"pid={os.getpid()}\n"
                         f"started={time.time():.0f}\n")
        except OSError:
            # Never fail a test because the advisory marker could not be
            # written -- it is a cleanup aid, not a correctness mechanism.
            pass
    return path


def sim_build_is_busy(path: str, max_age_s: int = 7200) -> Optional[dict]:
    """Return the owner's marker if this directory is actively being built in.

    LIVENESS IS THE TEST, NOT SESSION IDENTITY. An earlier version exempted
    "my own session", reasoning that a session may clean up after itself.
    That protected nobody: sim_session_id() is 'shared' for everyone who has
    not set SIM_BUILD_ROOT or SIM_SESSION_ID, so the common case compared
    'shared' to 'shared' and cleaned straight through live builds. Verified by
    racing the cleaner against a live run -- 10 removed, 0 skipped, and the
    original failure reproduced.

    A directory is busy when its marker names a pid that is STILL ALIVE and is
    not this process. Stale markers (dead owner, or older than max_age_s) are
    reclaimable. Session id is recorded and reported for diagnosis, but it
    never grants permission to delete.
    """
    marker = os.path.join(path, SIM_BUSY_MARKER)
    if not os.path.isfile(marker):
        return None
    info = {}
    try:
        for line in open(marker):
            if '=' in line:
                k, v = line.strip().split('=', 1)
                info[k] = v
    except OSError:
        return None

    try:
        if time.time() - float(info.get('started', 0)) > max_age_s:
            return None                    # abandoned long ago
    except (TypeError, ValueError):
        return None                        # unparseable marker: do not block

    pid = info.get('pid')
    if not (pid and pid.isdigit()):
        return None
    pid = int(pid)
    if pid == os.getpid():
        return None                        # our own marker
    try:
        os.kill(pid, 0)                    # signal 0 = liveness probe only
    except OSError:
        return None                        # owner is gone; safe to reclaim
    return info


def get_paths(dir_dict):
    """
    Returns module, repo_root, test_dir (relative to the calling file), log_dir, and a dictionary of additional paths.

    Args:
        dir_dict (dict): Dictionary where keys are tags and values are subdirectory paths.

    Returns:
        tuple: (module, repo_root, tests_dir, log_dir, paths_dict)
    """
    # Get the calling file's directory
    caller_frame = inspect.stack()[1]
    caller_file = caller_frame.filename
    tests_dir = os.path.abspath(os.path.dirname(caller_file))

    # Extract module name from the calling script
    module = os.path.splitext(os.path.basename(caller_file))[0]

    # Get repo root
    repo_root = get_repo_root()

    # Define common log directory
    log_dir = os.path.abspath(os.path.join(tests_dir, 'logs'))

    # Construct additional paths
    paths_dict = {key: os.path.abspath(os.path.join(repo_root, value)) for key, value in dir_dict.items()}

    return module, repo_root, tests_dir, log_dir, paths_dict


def preserve_prior_log(log_path, keep=3):
    """Rotate an existing log aside so a re-run cannot destroy its evidence.

    The log path is keyed by TEST NAME, so re-running a failing test overwrites
    the failing run's log -- including the SEED line the TB prints so the run
    can be reproduced. That is exactly the file you need, and it is gone the
    moment you try to look at the failure again.

    This is not hypothetical: a randomized descriptor soak failed in a full
    suite run and passed when re-run alone. The re-run overwrote the failing
    log, took the seed with it, and made it impossible to tell a seed-specific
    RTL bug from an environmental one. The failure is still unclassified.

    Keeps the previous `keep` runs as <name>.1.log (most recent) .. .N.log.
    Best-effort: a rotation failure must never fail a test, so errors are
    swallowed -- losing a rotation is bad, losing the run is worse.
    """
    try:
        if not os.path.isfile(log_path):
            return
        base, ext = os.path.splitext(log_path)
        for i in range(keep - 1, 0, -1):
            older, newer = f"{base}.{i}{ext}", f"{base}.{i + 1}{ext}"
            if os.path.isfile(older):
                os.replace(older, newer)
        os.replace(log_path, f"{base}.1{ext}")
    except OSError:
        pass


def create_view_cmd(log_dir, log_path, sim_build, module, test_name):
    """
    Creates a shell script to view waveforms and logs based on the simulator in use.

    If VCS is set in the environment, it generates a script using Verdi to view FSDB files.
    Otherwise, it uses GTKWave to view FST files.

    Args:
        log_dir (str): Directory where the script will be saved.
        log_path (str): Path to the log file.
        sim_build (str): Simulation build directory.
        module (str): Module name (used for waveform file naming).
        test_name (str): Test name (used for script naming).
    """
    mod_new = module.replace("test_", "", 1)
    cmd_filename = os.path.join(log_dir, f"view_{test_name}.sh")

    with open(cmd_filename, "w", encoding='utf-8') as cmd_file:
        cmd_file.write("#!/bin/bash\n")
        cmd_file.write("# To view waveforms: Run this script\n")

        if "VCS" in os.environ:
            cmd_file.write(f"cd {sim_build} && verdi -ssf {module}.fsdb\n")
        else:
            # Every wrapper sets TRACE_FILE={sim_build}/dump.fst -- the old
            # {module}.fst pointed at a file that never exists (test-audit
            # finding, math round_1).
            cmd_file.write(f"cd {sim_build} && gtkwave dump.fst\n")

        cmd_file.write(f"# To view logs: cat {log_path}\n")

    os.chmod(cmd_filename, 0o755)  # Make executable
    return cmd_filename


def get_wave_config(sim_build: str) -> Dict:
    """Resolve waveform configuration from environment variables.

    Honors:
        WAVES       '1' to enable waveform dumping, '0' (default) to disable.
        WAVES_TYPE  'fst' (default) or 'vcd'. Case-insensitive.

    Args:
        sim_build: Simulation build directory where the trace file will live.

    Returns:
        Dict with keys:
            enable      (bool)  Whether waveforms are enabled.
            fmt         (str)   'fst' or 'vcd'.
            extra_args  (list)  Verilator compile flags for trace support.
            sim_args    (list)  Runtime plus_args for the simulator.
            extra_env   (dict)  Env vars to merge into cocotb-test extra_env.
            trace_file  (str)   Absolute path to the dump file, or '' if disabled.
    """
    enable = bool(int(os.environ.get('WAVES', '0')))
    fmt = os.environ.get('WAVES_TYPE', 'fst').lower()
    if fmt not in ('fst', 'vcd'):
        fmt = 'fst'

    result: Dict = {
        'enable': enable,
        'fmt': fmt,
        'extra_args': [],
        'sim_args': [],
        'extra_env': {},
        'trace_file': '',
    }

    if not enable:
        return result

    trace_file = os.path.join(sim_build, f'dump.{fmt}')
    result['trace_file'] = trace_file
    result['extra_env'] = {'COCOTB_TRACE_FILE': trace_file}
    result['sim_args'] = ['--trace']

    if fmt == 'fst':
        result['extra_args'] = ['--trace-fst', '--trace-structs']
    else:
        result['extra_args'] = ['--trace', '--trace-structs']

    return result


def quick_log():
    log_file = tempfile.NamedTemporaryFile(delete=False, suffix=".log").name  # Create temp log file
    logging.basicConfig(filename=log_file, level=logging.DEBUG,
                        format="%(asctime)s - %(levelname)s - %(message)s")
    return logging.getLogger("quick_debug"), log_file


# ============================================================================
# Struct Extraction Utilities
# ============================================================================

def extract_struct_for_test(struct_file: str, struct_name: str, output_dir: str,
                            force_overwrite: bool = True) -> Dict:
    """
    Extract a struct definition and generate all necessary files for testing.

    This is the main function test runners should use for struct extraction.
    It integrates with the CocoTB framework infrastructure.

    Args:
        struct_file (str): Path to SystemVerilog file containing struct definitions
        struct_name (str): Name of struct to extract
        output_dir (str): Directory for generated files (typically sim_build)
        force_overwrite (bool): Whether to overwrite existing files

    Returns:
        dict: Dictionary containing:
            - success (bool): Whether extraction succeeded
            - struct_name (str): Name of the extracted struct
            - typedef_name (str): SystemVerilog typedef name
            - struct_content (str): Full struct definition
            - files_generated (dict): Paths to generated files
            - field_info (dict): Information about struct fields
            - validation (dict): Validation results

    Raises:
        RuntimeError: If extraction fails
        FileNotFoundError: If struct file doesn't exist
    """
    try:
        # Validate inputs
        if not os.path.exists(struct_file):
            raise FileNotFoundError(f"Struct file not found: {struct_file}")

        if not struct_name:
            raise ValueError("Struct name cannot be empty")

        # Create output directory
        os.makedirs(output_dir, exist_ok=True)

        # Parse the struct file
        parser = StructParser(struct_file)

        # Check if struct exists
        available_structs = parser.list_structs()
        if struct_name not in available_structs:
            raise ValueError(f"Struct '{struct_name}' not found. Available: {', '.join(available_structs)}")

        # Get struct information
        struct_info = parser.get_struct(struct_name)
        struct_content = struct_info['content']
        typedef_name = struct_info['typedef_name']
        field_info = struct_info['field_info']

        if not typedef_name:
            raise ValueError(f"Could not extract typedef name from struct '{struct_name}'")

        # Validate struct syntax
        is_valid, validation_msg = parser.validate_struct_syntax(struct_name)
        if not is_valid:
            raise ValueError(f"Invalid struct syntax: {validation_msg}")

        # Generate include file
        include_filename = f"generated_struct_{struct_name}.svh"
        include_file = os.path.join(output_dir, include_filename)

        if not force_overwrite and os.path.exists(include_file):
            raise FileExistsError(f"Include file already exists: {include_file}. Use force_overwrite=True")

        success = parser.generate_include_file(struct_name, include_file)
        if not success:
            raise RuntimeError("Failed to generate include file")

        # Generate Python helper file
        python_helpers_file = StructHelper.generate_python_helpers(
            struct_name, typedef_name, struct_content, field_info, output_dir
        )

        # Generate environment file
        env_file = StructHelper.generate_environment_file(
            struct_name, typedef_name, struct_content, include_file, python_helpers_file, output_dir
        )

        # Return comprehensive result
        result = {
            "success": True,
            "struct_name": struct_name,
            "typedef_name": typedef_name,
            "struct_content": struct_content,
            "files_generated": {
                "include_file": os.path.abspath(include_file),
                "python_helpers": os.path.abspath(python_helpers_file),
                "environment_file": os.path.abspath(env_file)
            },
            "field_info": field_info,
            "validation": {
                "valid": is_valid,
                "message": validation_msg
            },
            "bit_width": sum(field["width"] for field in field_info.values()) if field_info else 0
        }

        return result

    except Exception as e:
        # Re-raise with context
        raise RuntimeError(f"Struct extraction failed for '{struct_name}': {str(e)}") from e


def list_available_structs(struct_file: str) -> List[str]:
    """
    List all available structs in a SystemVerilog file.

    Args:
        struct_file (str): Path to SystemVerilog file containing struct definitions

    Returns:
        list: List of available struct names

    Raises:
        FileNotFoundError: If struct file doesn't exist
        RuntimeError: If file cannot be parsed
    """
    try:
        if not os.path.exists(struct_file):
            raise FileNotFoundError(f"Struct file not found: {struct_file}")

        parser = StructParser(struct_file)
        return parser.list_structs()

    except Exception as e:
        raise RuntimeError(f"Failed to list structs from {struct_file}: {str(e)}") from e


def validate_struct_file(struct_file: str, quiet: bool = False) -> Tuple[bool, str, List[str]]:
    """
    Validate a struct file and return detailed information.

    Args:
        struct_file (str): Path to SystemVerilog file to validate
        quiet (bool): If True, suppress detailed output

    Returns:
        tuple: (success, message, list_of_available_structs)
    """
    return validate_struct_setup(struct_file)


def get_struct_info(struct_file: str, struct_name: str) -> Optional[Dict]:
    """
    Get detailed information about a specific struct without generating files.

    Args:
        struct_file (str): Path to SystemVerilog file containing struct definitions
        struct_name (str): Name of struct to inspect

    Returns:
        dict: Struct information or None if not found
    """
    try:
        if not os.path.exists(struct_file):
            return None

        parser = StructParser(struct_file)
        struct_info = parser.get_struct(struct_name)

        if not struct_info:
            return None

        # Add validation info
        is_valid, validation_msg = parser.validate_struct_syntax(struct_name)
        struct_info['validation'] = {
            'valid': is_valid,
            'message': validation_msg
        }

        # Add bit width calculation
        field_info = struct_info.get('field_info', {})
        struct_info['bit_width'] = sum(field["width"] for field in field_info.values()) if field_info else 0

        return struct_info

    except Exception:
        return None


def setup_struct_environment(struct_info: Dict) -> Dict[str, str]:
    """
    Create environment variables dict from struct information.

    This is useful for test runners that need to pass struct info to cocotb tests.

    Args:
        struct_info (dict): Struct information from extract_struct_for_test()

    Returns:
        dict: Environment variables ready to be added to extra_env
    """
    if not struct_info.get('success', False):
        return {}

    return {
        'TEST_STRUCT_NAME': struct_info['struct_name'],
        'TEST_TYPEDEF_NAME': struct_info['typedef_name'],
        'TEST_STRUCT_FILE': struct_info['files_generated']['include_file'],
        'TEST_STRUCT_HELPERS': struct_info['files_generated']['python_helpers'],
        'TEST_STRUCT_CONTENT': struct_info['struct_content'],
        'TEST_STRUCT_BIT_WIDTH': str(struct_info['bit_width']),
    }


def find_struct_file(repo_root: str, search_paths: List[str] = None) -> Optional[str]:
    """
    Find the global struct file in common locations.

    Args:
        repo_root (str): Repository root directory
        search_paths (list): Additional paths to search (relative to repo_root)

    Returns:
        str: Path to struct file or None if not found
    """
    default_paths = [
        'rtl/amba/include/axi_structs.sv',
        'rtl/include/structs.sv',
        'include/axi_structs.sv',
        'include/structs.sv',
        'rtl/common/structs.sv'
    ]

    search_paths = search_paths or []
    all_paths = default_paths + search_paths

    for path in all_paths:
        full_path = os.path.join(repo_root, path)
        if os.path.exists(full_path):
            return full_path

    return None


def extract_struct_for_test_simple(struct_name: str, sim_build: str,
                                    repo_root: str = None, struct_file: str = None) -> Dict:
    """
    Simplified struct extraction function for test runners.

    This function automatically finds the struct file and extracts the struct.
    Perfect for test runners that just want to specify a struct name.

    Args:
        struct_name (str): Name of struct to extract
        sim_build (str): Simulation build directory
        repo_root (str): Repository root (auto-detected if None)
        struct_file (str): Path to struct file (auto-found if None)

    Returns:
        dict: Struct information (same as extract_struct_for_test)

    Raises:
        RuntimeError: If struct file cannot be found or extraction fails
    """
    # Auto-detect repo root if not provided
    if not repo_root:
        try:
            repo_root = get_repo_root()
        except subprocess.CalledProcessError:
            raise RuntimeError("Could not determine repository root and none provided")

    # Auto-find struct file if not provided
    if not struct_file:
        struct_file = find_struct_file(repo_root)
        if not struct_file:
            raise RuntimeError(f"Could not find struct file in repository. Searched common locations in {repo_root}")

    # Extract the struct
    return extract_struct_for_test(struct_file, struct_name, sim_build)


# ============================================================================
# Convenience Functions for Test Runners
# ============================================================================

def get_paths_with_struct(dir_dict: Dict[str, str], struct_name: str, sim_build: str = None) -> Tuple:
    """
    Extended version of get_paths that also extracts struct information.

    Args:
        dir_dict (dict): Dictionary for get_paths
        struct_name (str): Name of struct to extract
        sim_build (str): Simulation build directory (auto-generated if None)

    Returns:
        tuple: (module, repo_root, tests_dir, log_dir, paths_dict, struct_info)
    """
    # Get standard paths
    module, repo_root, tests_dir, log_dir, paths_dict = get_paths(dir_dict)

    # Auto-generate sim_build if not provided
    if not sim_build:
        sim_build = sim_build_path(tests_dir, f'{module}_{struct_name}')

    # Extract struct information
    try:
        struct_info = extract_struct_for_test_simple(struct_name, sim_build, repo_root)
    except Exception as e:
        # Return None for struct_info if extraction fails
        # This allows the test runner to handle the error gracefully
        struct_info = {'success': False, 'error': str(e)}

    return module, repo_root, tests_dir, log_dir, paths_dict, struct_info


def setup_struct_test_environment(struct_name: str, sim_build: str, base_env: Dict[str, str] = None) -> Dict[str, str]:
    """
    One-stop function to set up complete test environment with struct support.

    Args:
        struct_name (str): Name of struct to extract
        sim_build (str): Simulation build directory
        base_env (dict): Base environment variables to extend

    Returns:
        dict: Complete environment dictionary ready for cocotb
    """
    base_env = base_env or {}

    try:
        # Extract struct
        struct_info = extract_struct_for_test_simple(struct_name, sim_build)

        # Setup struct environment
        struct_env = setup_struct_environment(struct_info)

        # Combine environments
        complete_env = {**base_env, **struct_env}

        return complete_env

    except Exception as e:
        # Return base environment with error info if struct extraction fails
        error_env = {
            'TEST_STRUCT_ERROR': str(e),
            'TEST_STRUCT_NAME': struct_name,
        }
        return {**base_env, **error_env}


def get_wavejson_dir(module_name: str, tests_dir: str = None) -> str:
    """Where a wavedrom test should write its .json output.

    Defaults to <repo>/docs/markdown/assets/WAVES/staged/<module_name> -- a
    staging area NEXT to the production diagrams but gitignored, so a run
    never clobbers the committed WAVES/<module>/ files and there is nothing
    to back out afterwards. Review the staged output, then promote the files
    you actually want by copying them up one level.

    Wavedrom output is NOT deterministic -- two consecutive runs of the same
    test produce different waveform lengths -- which is why the default must
    never be the tracked directory.

    Set WAVEJSON_DIR to publish directly instead of staging, e.g. when you
    intend to refresh the committed diagrams:

        WAVEJSON_DIR=docs/markdown/assets/WAVES pytest val/cdc/test_fifo_async_wavedrom.py

    The module name is appended to WAVEJSON_DIR, matching the committed
    layout. `tests_dir` is accepted for backward compatibility and ignored.
    """
    import os as _os

    override = _os.environ.get('WAVEJSON_DIR')
    if override:
        return _os.path.abspath(_os.path.join(override, module_name))

    repo_root = _os.path.dirname(_os.path.dirname(_os.path.dirname(
        _os.path.dirname(_os.path.abspath(__file__)))))
    return _os.path.join(repo_root, 'docs', 'markdown', 'assets', 'WAVES',
                         'staged', module_name)
