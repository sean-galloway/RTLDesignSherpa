# utilities.py

Common utilities for path management, environment setup, and tool integration in the CocoTBFramework. This module provides essential functions for automating development environment setup, path resolution, and simulator integration.

## Overview

The `utilities.py` module contains utility functions that bridge the gap between Python testbenches and the broader development ecosystem. It provides automatic path discovery, environment configuration, simulator detection, and waveform viewer integration.

### Key Features
- **Automatic path resolution** using Git repository detection
- **Cross-platform compatibility** (Windows, Linux, macOS)
- **Simulator detection and configuration** (VCS, Questasim, Xcelium, etc.)
- **Waveform viewer integration** (GTKWave, Verdi)
- **Build system integration** and environment setup
- **Modular design** for easy integration into existing flows

## Core Functions

### `get_paths(dir_dict)`

Automatically resolves project paths using Git repository detection and returns standardized path structure.

**Parameters:**
- `dir_dict`: Dictionary mapping path tags to relative subdirectory paths

**Returns:** Tuple of `(module, repo_root, tests_dir, log_dir, paths_dict)`

```python
# Define project structure
path_config = {
    'rtl': 'hardware/rtl',
    'tb': 'verification/testbench',
    'scripts': 'scripts',
    'docs': 'documentation'
}

# Get resolved paths
module, repo_root, tests_dir, log_dir, paths = get_paths(path_config)

print(f"Module: {module}")
print(f"Repository root: {repo_root}")
print(f"Test directory: {tests_dir}")
print(f"Log directory: {log_dir}")
print(f"RTL path: {paths['rtl']}")
print(f"Testbench path: {paths['tb']}")
```

**Return Values:**
- `module`: Module name extracted from calling script filename
- `repo_root`: Git repository root directory (absolute path)
- `tests_dir`: Directory containing the calling script (absolute path)
- `log_dir`: Log directory (tests_dir/logs, absolute path)
- `paths_dict`: Dictionary of absolute paths for each key in dir_dict

**Example Output:**
```python
module = "memory_test"
repo_root = "/home/user/my_project"
tests_dir = "/home/user/my_project/verification/tests"
log_dir = "/home/user/my_project/verification/tests/logs"
paths = {
    'rtl': "/home/user/my_project/hardware/rtl",
    'tb': "/home/user/my_project/verification/testbench",
    'scripts': "/home/user/my_project/scripts",
    'docs': "/home/user/my_project/documentation"
}
```

### `create_view_cmd(log_dir, log_path, sim_build, module, test_name)`

Creates shell scripts for viewing waveforms and logs with automatic simulator detection.

**Parameters:**
- `log_dir`: Directory where the script will be saved
- `log_path`: Path to the simulation log file
- `sim_build`: Simulation build directory containing waveform files
- `module`: Module name (used for waveform file naming)
- `test_name`: Test name (used for script naming and file identification)

```python
# Create waveform viewing script
create_view_cmd(
    log_dir=log_dir,
    log_path=f"{log_dir}/{module}.log",
    sim_build="./sim_build",
    module="memory_controller",
    test_name="basic_read_write"
)

# This creates: {log_dir}/view_basic_read_write.sh
```

**Generated Script Behavior:**
- **VCS Environment**: Creates Verdi script for viewing FSDB files
- **Other Simulators**: Creates GTKWave script for viewing FST files
- **Automatic Detection**: Checks `VCS` environment variable to determine simulator
- **Log Integration**: Includes commands to view simulation logs alongside waveforms

**VCS/Verdi Script Example:**
```bash
#!/bin/bash
echo "Opening Verdi with FSDB waveform..."
verdi -ssf ./sim_build/memory_controller.fsdb -nologo &
echo "Opening simulation log..."
gedit /path/to/logs/memory_controller.log &
```

**GTKWave Script Example:**
```bash
#!/bin/bash
echo "Opening GTKWave with FST waveform..."
gtkwave ./sim_build/memory_controller.fst &
echo "Opening simulation log..."
gedit /path/to/logs/memory_controller.log &
```

## Path Resolution Details

### Git Integration

The `get_paths()` function uses Git to automatically discover the project structure:

```python
# Uses git rev-parse --show-toplevel to find repository root
repo_root = subprocess.check_output([
    'git', 'rev-parse', '--show-toplevel'
]).strip().decode('utf-8')
```

**Benefits:**
- **No manual configuration**: Automatically adapts to different checkout locations
- **Team consistency**: Same paths regardless of where team members check out code
- **CI/CD friendly**: Works in automated build environments
- **Submodule support**: Properly handles Git submodules and nested repositories

### Calling Context Detection

The module automatically detects the calling script's context:

```python
# Extracts module name from calling script
caller_frame = inspect.stack()[1]
caller_file = caller_frame.filename
module = os.path.splitext(os.path.basename(caller_file))[0]
```

**Use Cases:**
- Test scripts automatically get their name as module identifier
- Log files are named based on the calling script
- Waveform files use consistent naming conventions
- Report generation uses appropriate identifiers

## Environment Detection

### Simulator Detection

The utilities automatically detect the simulation environment:

```python
# VCS detection
if 'VCS' in os.environ:
    # Use Verdi for waveform viewing
    create_verdi_script(...)
else:
    # Use GTKWave for waveform viewing
    create_gtkwave_script(...)
```

**Supported Simulators:**
- **Synopsys VCS**: Uses Verdi for waveform viewing with FSDB files
- **Mentor Questasim**: Uses ModelSim or GTKWave for viewing
- **Cadence Xcelium**: Uses SimVision or GTKWave for viewing
- **Open Source**: Uses GTKWave with FST/VCD files

### Cross-Platform Support

The utilities handle platform-specific differences:

```python
# Platform-specific editor detection
if platform.system() == "Windows":
    editor = "notepad"
elif platform.system() == "Darwin":  # macOS
    editor = "open -t"
else:  # Linux
    editor = "gedit"
```

**Platform Adaptations:**
- **Path separators**: Automatic handling of Windows vs Unix paths
- **Editor selection**: Platform-appropriate text editors
- **Shell scripts**: Batch files on Windows, shell scripts on Unix
- **Tool paths**: Automatic detection of tool installation locations

## Integration Patterns

### Basic Test Script Setup

```python
#!/usr/bin/env python3

import cocotb
from CocoTBFramework.tbclasses.misc.utilities import get_paths, create_view_cmd

# Automatic path setup
module, repo_root, tests_dir, log_dir, paths = get_paths({
    'rtl': 'rtl',
    'tb': 'testbench',
    'scripts': 'scripts'
})

@cocotb.test()
async def my_test(dut):
    # Your test implementation
    pass

# Create waveform viewing script
create_view_cmd(
    log_dir=log_dir,
    log_path=f"{log_dir}/{module}.log",
    sim_build="./sim_build",
    module=module,
    test_name="my_test"
)
```

### Makefile Integration

```makefile
# Makefile that uses utilities-generated paths
SHELL := /bin/bash

# Python script generates these paths
PATHS := $(shell python3 -c "from utilities import get_paths; print(' '.join(get_paths({'rtl': 'rtl'})[:4]))")
MODULE := $(word 1,$(PATHS))
REPO_ROOT := $(word 2,$(PATHS))
TESTS_DIR := $(word 3,$(PATHS))
LOG_DIR := $(word 4,$(PATHS))

# Use generated paths in simulation
sim:
    @echo "Running $(MODULE) test..."
    @mkdir -p $(LOG_DIR)
    cocotb-run --log-dir=$(LOG_DIR) ...
    
view:
    @if [ -f $(LOG_DIR)/view_$(MODULE).sh ]; then \
        chmod +x $(LOG_DIR)/view_$(MODULE).sh; \
        $(LOG_DIR)/view_$(MODULE).sh; \
    else \
        echo "No view script found. Run simulation first."; \
    fi
```

### CI/CD Integration

```yaml
# GitHub Actions example
name: Verification
on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v2
    
    - name: Setup Python
      uses: actions/setup-python@v2
      with:
        python-version: '3.8'
    
    - name: Install dependencies
      run: |
        pip install cocotb
        pip install -e .
    
    - name: Run tests
      run: |
        cd verification/tests
        python3 test_memory.py
        
    - name: Archive logs
      uses: actions/upload-artifact@v2
      with:
        name: simulation-logs
        path: verification/tests/logs/
```

### Advanced Project Structure

```python
# Complex project with multiple test directories
def setup_verification_environment():
    """Setup comprehensive verification environment"""
    
    # Define complex path structure
    path_config = {
        'rtl': 'hardware/rtl',
        'tb': 'verification/testbench',
        'tests': 'verification/tests',
        'scripts': 'verification/scripts',
        'docs': 'docs/verification',
        'reports': 'reports',
        'coverage': 'coverage',
        'waves': 'waves'
    }
    
    # Get resolved paths
    module, repo_root, tests_dir, log_dir, paths = get_paths(path_config)
    
    # Create additional directories
    os.makedirs(paths['reports'], exist_ok=True)
    os.makedirs(paths['coverage'], exist_ok=True)
    os.makedirs(paths['waves'], exist_ok=True)
    
    # Setup environment variables
    os.environ['VERIFICATION_ROOT'] = paths['tb']
    os.environ['RTL_ROOT'] = paths['rtl']
    os.environ['TEST_ROOT'] = paths['tests']
    
    return {
        'module': module,
        'repo_root': repo_root,
        'tests_dir': tests_dir,
        'log_dir': log_dir,
        'paths': paths
    }

# Use in test scripts
env = setup_verification_environment()
module = env['module']
paths = env['paths']
```

## Best Practices

### Path Management
- **Use get_paths() early**: Call at the beginning of test scripts
- **Consistent structure**: Maintain consistent directory naming across projects
- **Relative paths in config**: Use relative paths in dir_dict for portability
- **Version control**: Don't version control generated scripts and logs

### Environment Setup
- **Minimal assumptions**: Don't assume specific tool installations
- **Graceful degradation**: Provide fallbacks when tools aren't available
- **Documentation**: Document required environment variables and tools
- **Testing**: Test utilities on different platforms and environments

### Integration
- **Makefile cooperation**: Design Makefiles to work with utilities
- **CI/CD friendly**: Ensure utilities work in automated environments
- **Tool agnostic**: Don't hardcode specific tool paths or versions
- **Error handling**: Provide clear error messages for missing dependencies

### Development Workflow
- **View script generation**: Always generate view scripts for debugging
- **Log organization**: Use consistent log file naming and organization
- **Waveform management**: Organize waveforms by test and module
- **Report integration**: Integrate with existing reporting systems

The utilities module provides essential infrastructure for creating portable, maintainable verification environments that work consistently across different development setups, platforms, and tool chains.