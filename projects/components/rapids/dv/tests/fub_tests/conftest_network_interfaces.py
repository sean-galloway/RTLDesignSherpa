"""
RAPIDS Validation Test Configuration for pytest

Configures the test environment for RAPIDS (Memory Input/Output Processor) validation,
following the established repository patterns while adding RAPIDS-specific settings.
"""

import os
import logging
import pytest

# Configure pytest to always collect logs
def pytest_configure(config):
    # Create logs directory if it doesn't exist
    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)

    # Configure log file for pytest itself
    config.option.log_file = os.path.join(log_dir, "pytest_rapids.log")
    config.option.log_file_level = "DEBUG"

    # Enable console logging
    config.option.log_cli = True
    config.option.log_cli_level = "INFO"

    # Register RAPIDS-specific pytest markers
    # Test type markers
    config.addinivalue_line("markers", "fub: FUB (Functional Unit Block) level tests")
    config.addinivalue_line("markers", "macro: Macro block integration tests")
    config.addinivalue_line("markers", "integration: System integration tests")

    # Component markers
    config.addinivalue_line("markers", "scheduler: Scheduler component tests")
    config.addinivalue_line("markers", "descriptor: Descriptor engine tests")
    config.addinivalue_line("markers", "program: Program engine tests")
    config.addinivalue_line("markers", "axi: AXI engine tests")
    config.addinivalue_line("markers", "sram: SRAM control tests")
    config.addinivalue_line("markers", "mnoc: Network interface tests")
    config.addinivalue_line("markers", "monitor: Monitor bus tests")

    # Performance markers
    config.addinivalue_line("markers", "performance: Performance characterization tests")
    config.addinivalue_line("markers", "stress: Stress testing")
    config.addinivalue_line("markers", "regression: Regression test suite")

    # Additional custom markers that were showing up in tests
    config.addinivalue_line("markers", "rapids: RAPIDS-related tests")
    config.addinivalue_line("markers", "alignment: Alignment bus tests")

# Preserve all files regardless of test outcome
@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    """
    Called after whole test run finished, right before returning the exit status.
    """
    logging.info("RAPIDS test session finished. Preserving all logs and build artifacts.")

# Disable automatic test collection in the logs directory if it exists
def pytest_ignore_collect(collection_path, config):
    return 'logs' in str(collection_path)

# RAPIDS-specific test parametrization fixtures
@pytest.fixture(scope="module", params=[
    # Channel configurations: (num_channels, chan_width, lines_per_channel)
    (2, 1, 256),     # Minimal 2-channel configuration
    (8, 3, 256),     # Small 8-channel configuration
    (16, 4, 256),    # Medium 16-channel configuration
    (32, 5, 256),    # Full 32-channel configuration
])
def rapids_channel_config(request):
    """RAPIDS channel configuration parameters"""
    num_channels, chan_width, lines_per_channel = request.param
    return {
        'NUM_CHANNELS': num_channels,
        'CHAN_WIDTH': chan_width,
        'LINES_PER_CHANNEL': lines_per_channel
    }

@pytest.fixture(scope="module", params=[
    # Data configurations: (data_width, addr_width, num_chunks, axi_id_width)
    (512, 64, 16, 8),   # Standard RAPIDS configuration
    (256, 32, 8, 4),    # Reduced width configuration
])
def rapids_data_config(request):
    """RAPIDS data width configuration parameters"""
    data_width, addr_width, num_chunks, axi_id_width = request.param
    return {
        'DATA_WIDTH': data_width,
        'ADDR_WIDTH': addr_width,
        'NUM_CHUNKS': num_chunks,
        'AXI_ID_WIDTH': axi_id_width
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

@pytest.fixture(scope="module", params=[
    # Timing configurations: (profile, description, setup_cycles, hold_cycles, backpressure_ratio)
    ('normal', 'Normal timing', 1, 1, 0.1),
    ('fast', 'Fast timing', 0, 0, 0.0),
    ('slow', 'Slow timing', 3, 3, 0.3),
    ('stress', 'Stress timing', 5, 2, 0.5),
])
def rapids_timing_config(request):
    """RAPIDS timing profile configuration"""
    profile, description, setup_cycles, hold_cycles, backpressure_ratio = request.param
    return {
        'profile': profile,
        'description': description,
        'setup_cycles': setup_cycles,
        'hold_cycles': hold_cycles,
        'backpressure_ratio': backpressure_ratio
    }

@pytest.fixture(scope="module", params=[
    # Protocol configurations: (protocol, enable_eos, enable_credit, enable_monitor)
    ('standard', True, True, True),     # Full RAPIDS protocol
    ('minimal', True, False, False),    # Minimal protocol features
    ('no_eos', False, True, True),      # No EOS boundaries
])
def rapids_protocol_config(request):
    """RAPIDS protocol feature configuration"""
    protocol, enable_eos, enable_credit, enable_monitor = request.param
    return {
        'protocol': protocol,
        'enable_eos': enable_eos,
        'enable_credit': enable_credit,
        'enable_monitor': enable_monitor
    }

# RAPIDS-specific environment variable helpers
def get_rapids_env_config():
    """Get RAPIDS configuration from environment variables"""
    return {
        'NUM_CHANNELS': int(os.environ.get('RAPIDS_NUM_CHANNELS', '8')),
        'DATA_WIDTH': int(os.environ.get('RAPIDS_DATA_WIDTH', '512')),
        'ADDR_WIDTH': int(os.environ.get('RAPIDS_ADDR_WIDTH', '64')),
        'NUM_CHUNKS': int(os.environ.get('RAPIDS_NUM_CHUNKS', '16')),
        'AXI_ID_WIDTH': int(os.environ.get('RAPIDS_AXI_ID_WIDTH', '8')),
        'LINES_PER_CHANNEL': int(os.environ.get('RAPIDS_LINES_PER_CHANNEL', '256')),
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', 'basic').lower(),
        'ENABLE_COVERAGE': os.environ.get('ENABLE_COVERAGE', '0') == '1',
        'ENABLE_WAVEDUMP': os.environ.get('ENABLE_WAVEDUMP', '1') == '1',
    }

# Test collection hooks for RAPIDS-specific organization
def pytest_collection_modifyitems(config, items):
    """Modify test collection to add RAPIDS-specific markers"""
    for item in items:
        # Add markers based on test file patterns
        if "fub" in item.nodeid:
            item.add_marker(pytest.mark.fub)
        elif "macro" in item.nodeid:
            item.add_marker(pytest.mark.macro)
        elif "e2e" in item.nodeid or "integration" in item.nodeid:
            item.add_marker(pytest.mark.integration)

        # Add component-specific markers
        component_markers = {
            'scheduler': 'scheduler',
            'descriptor': 'descriptor',
            'program': 'program',
            'axi': 'axi',
            'sram': 'sram',
            'mnoc': 'mnoc',
            'monitor': 'monitor'
        }

        for component, marker in component_markers.items():
            if component in item.nodeid.lower():
                item.add_marker(getattr(pytest.mark, marker))

