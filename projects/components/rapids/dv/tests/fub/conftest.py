"""
RAPIDS FUB (Legacy Network-Based) Validation Test Configuration for pytest

Configures the test environment for RAPIDS FUB (Functional Unit Block) validation.
These modules use the legacy network-based interfaces (not AXIS).

Modules Tested:
- ctrlwr_engine: Control write engine for pre-descriptor operations
- ctrlrd_engine: Control read engine with retry mechanism
"""

import os
import sys
import logging
import pytest

# Configure pytest to always collect logs
def pytest_configure(config):
    # Add RAPIDS DV directory to path BEFORE pytest imports test modules
    # CRITICAL: Must be at position 0, even if already in sys.path from PYTHONPATH
    rapids_dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..'))

    # Remove if already present (from PYTHONPATH), then insert at position 0
    if rapids_dv_path in sys.path:
        sys.path.remove(rapids_dv_path)
    sys.path.insert(0, rapids_dv_path)

    # Create logs directory if it doesn't exist
    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)

    # Configure log file for pytest itself
    config.option.log_file = os.path.join(log_dir, "pytest_rapids_fub.log")
    config.option.log_file_level = "DEBUG"

    # Enable console logging
    config.option.log_cli = True
    config.option.log_cli_level = "INFO"

    # Register RAPIDS-specific pytest markers
    # Test type markers
    config.addinivalue_line("markers", "fub: FUB (Functional Unit Block) level tests")
    config.addinivalue_line("markers", "ctrlwr: Control write engine tests")
    config.addinivalue_line("markers", "ctrlrd: Control read engine tests")

    # Performance markers
    config.addinivalue_line("markers", "stress: Stress testing")
    config.addinivalue_line("markers", "regression: Regression test suite")
    config.addinivalue_line("markers", "error: Error injection tests")

# Preserve all files regardless of test outcome
@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    """
    Called after whole test run finished, right before returning the exit status.
    """
    logging.info("RAPIDS FUB test session finished. Preserving all logs and build artifacts.")

# Disable automatic test collection in the logs directory if it exists
def pytest_ignore_collect(collection_path, config):
    return 'logs' in str(collection_path) or 'local_sim_build' in str(collection_path)

# RAPIDS FUB-specific test parametrization fixtures
@pytest.fixture(scope="module", params=[
    # Channel configurations: (channel_id, num_channels, addr_width)
    (0, 8, 64),      # Default configuration
])
def rapids_fub_config(request):
    """RAPIDS FUB configuration parameters"""
    channel_id, num_channels, addr_width = request.param
    return {
        'CHANNEL_ID': channel_id,
        'NUM_CHANNELS': num_channels,
        'ADDR_WIDTH': addr_width,
    }

@pytest.fixture(scope="module", params=[
    # Test levels: (level, description, transaction_count, timeout_factor)
    ('basic', 'Basic functionality', 10, 1.0),
    ('medium', 'Medium stress testing', 50, 1.5),
    ('full', 'Full comprehensive testing', 200, 2.0),
])
def rapids_test_level(request):
    """RAPIDS test level configuration"""
    level, description, transaction_count, timeout_factor = request.param

    # Override from environment if specified
    env_level = os.environ.get('TEST_LEVEL', level).lower()
    if env_level in ['basic', 'medium', 'full']:
        level = env_level

    return {
        'level': level,
        'description': description,
        'transaction_count': transaction_count,
        'timeout_factor': timeout_factor
    }

# RAPIDS-specific environment variable helpers
def get_rapids_fub_env_config():
    """Get RAPIDS FUB configuration from environment variables"""
    return {
        'CHANNEL_ID': int(os.environ.get('RAPIDS_CHANNEL_ID', '0')),
        'NUM_CHANNELS': int(os.environ.get('RAPIDS_NUM_CHANNELS', '8')),
        'ADDR_WIDTH': int(os.environ.get('RAPIDS_ADDR_WIDTH', '64')),
        'AXI_ID_WIDTH': int(os.environ.get('RAPIDS_AXI_ID_WIDTH', '8')),
        'AXI_DATA_WIDTH': int(os.environ.get('RAPIDS_AXI_DATA_WIDTH', '64')),
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', 'basic').lower(),
        'ENABLE_COVERAGE': os.environ.get('ENABLE_COVERAGE', '0') == '1',
        'ENABLE_WAVEDUMP': os.environ.get('ENABLE_WAVEDUMP', '1') == '1',
    }

# Test collection hooks for RAPIDS-specific organization
def pytest_collection_modifyitems(config, items):
    """Modify test collection to add RAPIDS-specific markers"""
    for item in items:
        # Add FUB marker to all tests in this directory
        item.add_marker(pytest.mark.fub)

        # Add component-specific markers
        if 'ctrlwr' in item.nodeid.lower():
            item.add_marker(pytest.mark.ctrlwr)
        if 'ctrlrd' in item.nodeid.lower():
            item.add_marker(pytest.mark.ctrlrd)
