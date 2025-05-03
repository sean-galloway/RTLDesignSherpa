# Utilities Module Documentation

## Overview
The `utilities.py` module provides essential utility functions for the CocoTB verification flow. It includes functions for:
- Path management and directory structure setup
- Creating scripts for viewing waveforms and logs
- Quick logging setup

## Functions

### `get_paths(dir_dict)`
```python
def get_paths(dir_dict):
    """
    Returns module, repo_root, test_dir (relative to the calling file), log_dir, and a dictionary of additional paths.
    """
```

#### Purpose
This function establishes a consistent directory structure for tests by:
1. Identifying the calling file's directory
2. Finding the Git repository root
3. Setting up logging directories
4. Creating additional path mappings as specified

#### Arguments
- `dir_dict` (dict): Dictionary where keys are tags and values are subdirectory paths.

#### Returns
- Tuple: `(module, repo_root, tests_dir, log_dir, paths_dict)`
  - `module`: Name of the calling module extracted from filename
  - `repo_root`: Root of the Git repository
  - `tests_dir`: Directory containing the calling test
  - `log_dir`: Directory for test logs
  - `paths_dict`: Dictionary of additional paths based on input `dir_dict`

#### Usage Example
```python
# Define custom directories
dirs = {
    'rtl': 'rtl/src',
    'tb': 'tb/cocotb',
    'build': 'build/sim'
}

# Get path information
module, repo_root, tests_dir, log_dir, paths = get_paths(dirs)

# Use paths in test setup
print(f"Running test {module} from {tests_dir}")
print(f"Logs will be written to {log_dir}")
print(f"RTL path: {paths['rtl']}")
```

### `create_view_cmd(log_dir, log_path, sim_build, module, test_name)`
```python
def create_view_cmd(log_dir, log_path, sim_build, module, test_name):
    """
    Creates a shell script to view waveforms and logs based on the simulator in use.
    """
```

#### Purpose
Generates a shell script that helps view simulation results by:
1. Detecting the simulator being used (VCS or others)
2. Creating a script that launches the appropriate waveform viewer (Verdi for VCS, GTKWave for others)
3. Including commands to view log files

#### Arguments
- `log_dir` (str): Directory where the script will be saved
- `log_path` (str): Path to the log file
- `sim_build` (str): Simulation build directory
- `module` (str): Module name (used for waveform file naming)
- `test_name` (str): Test name (used for script naming)

#### Returns
- `cmd_filename` (str): Path to the created script

#### Usage Example
```python
# After test completion
view_script = create_view_cmd(
    log_dir="./logs",
    log_path="./logs/test.log",
    sim_build="./build",
    module="test_my_module",
    test_name="basic_test"
)
print(f"To view results, run: {view_script}")
```

### `quick_log()`
```python
def quick_log():
    """Creates and returns a quick logger and its log file path"""
```

#### Purpose
Creates a temporary logger for quick debugging without needing a full TBBase instance.

#### Returns
- Tuple: `(logger, log_file)`
  - `logger`: Configured logging.Logger instance
  - `log_file`: Path to the temporary log file

#### Usage Example
```python
# For quick debug sessions outside of a testbench
logger, log_file = quick_log()
logger.debug("Starting debug session")
logger.info("Testing function X")
logger.error("Error in function X")
print(f"Debug log saved to: {log_file}")
```

## Integration with CocoTB Framework
The utilities module is designed to work seamlessly with the CocoTB framework and other components like `TBBase`. Together they provide:

1. Consistent directory structure and path management
2. Standardized logging
3. Easy access to simulation results
4. Integration with version control

This module simplifies the setup and management of verification environments, allowing test authors to focus on test logic rather than infrastructure setup.
