# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: utilities
# Purpose: Returns module, repo_root, test_dir (relative to the calling file), log_dir, and
#
# Documentation: bin/CocoTBFramework/README.md
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
from typing import Dict, Tuple, Optional, List


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
    repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')

    # Define common log directory
    log_dir = os.path.abspath(os.path.join(tests_dir, 'logs'))

    # Construct additional paths
    paths_dict = {key: os.path.abspath(os.path.join(repo_root, value)) for key, value in dir_dict.items()}

    return module, repo_root, tests_dir, log_dir, paths_dict


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
            cmd_file.write(f"cd {sim_build} && gtkwave {mod_new}.fst\n")

        cmd_file.write(f"# To view logs: cat {log_path}\n")

    os.chmod(cmd_filename, 0o755)  # Make executable
    return cmd_filename


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
            repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
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
        sim_build = os.path.join(tests_dir, 'local_sim_build', f'{module}_{struct_name}')

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
