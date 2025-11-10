"""
Bridge Validation Test Configuration for pytest

Configures the test environment for AXI4 Bridge crossbar validation,
following the established repository patterns.
"""

import os
import sys
import logging
import pytest

# Add repository paths before any test imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, repo_root)
sys.path.insert(0, os.path.join(repo_root, 'bin'))


def pytest_configure(config):
    """Configure pytest for Bridge testing"""
    # Create logs directory if it doesn't exist
    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)

    # Configure log file for pytest itself
    config.option.log_file = os.path.join(log_dir, "pytest_bridge.log")
    config.option.log_file_level = "DEBUG"

    # Enable console logging
    config.option.log_cli = True
    config.option.log_cli_level = "INFO"

    # Register Bridge-specific pytest markers
    config.addinivalue_line("markers", "bridge: Bridge crossbar tests")
    config.addinivalue_line("markers", "basic: Basic functionality tests")
    config.addinivalue_line("markers", "routing: Address decode and routing tests")
    config.addinivalue_line("markers", "arbitration: Round-robin arbitration tests")
    config.addinivalue_line("markers", "concurrent: Concurrent path tests")
    config.addinivalue_line("markers", "stress: Stress testing")


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    """Called after whole test run finished"""
    logging.info("Bridge test session finished. Preserving all logs and build artifacts.")


def pytest_ignore_collect(collection_path, config):
    """Disable automatic test collection in logs directory"""
    return 'logs' in str(collection_path)


# Bridge-specific parametrization fixtures
@pytest.fixture(scope="module", params=[
    # (num_masters, num_slaves, data_width, addr_width, id_width)
    (2, 2, 32, 32, 4),   # Basic 2x2 crossbar
    (2, 4, 32, 32, 4),   # 2 masters, 4 slaves
    (4, 2, 32, 32, 4),   # 4 masters, 2 slaves
    (4, 4, 32, 32, 4),   # Full 4x4 crossbar
])
def bridge_config(request):
    """Bridge crossbar configuration parameters"""
    num_masters, num_slaves, data_width, addr_width, id_width = request.param
    return {
        'NUM_MASTERS': num_masters,
        'NUM_SLAVES': num_slaves,
        'DATA_WIDTH': data_width,
        'ADDR_WIDTH': addr_width,
        'ID_WIDTH': id_width,
    }


@pytest.fixture(scope="module", params=[
    # Test levels: (level, transaction_count, timeout_factor)
    ('basic', 10, 1.0),
    ('medium', 50, 1.5),
    ('full', 200, 2.0),
])
def bridge_test_level(request):
    """Bridge test level configuration"""
    level, transaction_count, timeout_factor = request.param

    # Override from environment if specified
    env_level = os.environ.get('TEST_LEVEL', level).lower()
    if env_level in ['basic', 'medium', 'full']:
        level = env_level

    return {
        'level': level,
        'transaction_count': transaction_count,
        'timeout_factor': timeout_factor
    }


def get_bridge_env_config():
    """Get Bridge configuration from environment variables"""
    return {
        'NUM_MASTERS': int(os.environ.get('BRIDGE_NUM_MASTERS', '2')),
        'NUM_SLAVES': int(os.environ.get('BRIDGE_NUM_SLAVES', '2')),
        'DATA_WIDTH': int(os.environ.get('BRIDGE_DATA_WIDTH', '32')),
        'ADDR_WIDTH': int(os.environ.get('BRIDGE_ADDR_WIDTH', '32')),
        'ID_WIDTH': int(os.environ.get('BRIDGE_ID_WIDTH', '4')),
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', 'basic').lower(),
        'ENABLE_WAVEDUMP': os.environ.get('ENABLE_WAVEDUMP', '1') == '1',
    }


def pytest_collection_modifyitems(config, items):
    """Modify test collection to add Bridge-specific markers"""
    for item in items:
        # Add markers based on test name patterns
        if "routing" in item.nodeid:
            item.add_marker(pytest.mark.routing)
        elif "arbitration" in item.nodeid:
            item.add_marker(pytest.mark.arbitration)
        elif "concurrent" in item.nodeid:
            item.add_marker(pytest.mark.concurrent)
        elif "stress" in item.nodeid:
            item.add_marker(pytest.mark.stress)
        elif "basic" in item.nodeid:
            item.add_marker(pytest.mark.basic)
