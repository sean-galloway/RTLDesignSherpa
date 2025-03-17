'''Various Utilities for the CocoTB Flow'''
import os
import subprocess
import inspect
import logging
import tempfile

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
