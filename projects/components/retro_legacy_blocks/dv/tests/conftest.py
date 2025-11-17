"""
APB HPET Test Configuration for pytest

Configures the test environment for APB HPET (High Precision Event Timer) validation,
following the established repository patterns for component testing.
"""

import os
import logging
import pytest

# Preserve all files regardless of test outcome
@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    """
    Called after whole test run finished, right before returning the exit status.
    """
    logging.info("APB HPET test session finished. Preserving all logs and build artifacts.")

# Disable automatic test collection in the logs directory if it exists
def pytest_ignore_collect(collection_path, config):
    return 'logs' in str(collection_path)

# APB HPET-specific test parametrization fixtures
@pytest.fixture(scope="module", params=[
    # Timer configurations: (num_timers, vendor_id, revision_id, description)
    (2, 0x8086, 1, "2-timer Intel-like"),
    (3, 0x1022, 2, "3-timer AMD-like"),
    (8, 0x43981, 16, "8-timer custom"),
])
def hpet_timer_config(request):
    """APB HPET timer configuration parameters"""
    num_timers, vendor_id, revision_id, description = request.param
    return {
        'NUM_TIMERS': num_timers,
        'VENDOR_ID': vendor_id,
        'REVISION_ID': revision_id,
        'description': description
    }

@pytest.fixture(scope="module", params=[
    # CDC configurations: (cdc_enable, description)
    (0, "no CDC"),
    (1, "with CDC"),
])
def hpet_cdc_config(request):
    """APB HPET clock domain crossing configuration"""
    cdc_enable, description = request.param
    return {
        'CDC_ENABLE': cdc_enable,
        'description': description
    }

@pytest.fixture(scope="module", params=[
    # Test levels: (level, description, test_count, timeout_factor)
    ('basic', 'Basic functionality', 4, 1.0),
    ('medium', 'Medium stress testing', 5, 1.5),
    ('full', 'Full comprehensive testing', 3, 2.0),
])
def hpet_test_level(request):
    """APB HPET test level configuration"""
    level, description, test_count, timeout_factor = request.param

    # Override from environment if specified
    env_level = os.environ.get('TEST_LEVEL', level).lower()
    if env_level in ['basic', 'medium', 'full']:
        level = env_level

    return {
        'level': level,
        'description': description,
        'test_count': test_count,
        'timeout_factor': timeout_factor
    }

@pytest.fixture(scope="module", params=[
    # Timer mode configurations: (mode, description)
    ('one-shot', 'One-shot mode'),
    ('periodic', 'Periodic mode'),
])
def hpet_timer_mode(request):
    """APB HPET timer mode configuration"""
    mode, description = request.param
    return {
        'mode': mode,
        'description': description
    }

# APB HPET-specific environment variable helpers
def get_hpet_env_config():
    """Get APB HPET configuration from environment variables"""
    return {
        'NUM_TIMERS': int(os.environ.get('HPET_NUM_TIMERS', '2')),
        'VENDOR_ID': int(os.environ.get('HPET_VENDOR_ID', '0x8086')),
        'REVISION_ID': int(os.environ.get('HPET_REVISION_ID', '1')),
        'CDC_ENABLE': int(os.environ.get('HPET_CDC_ENABLE', '0')),
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', 'basic').lower(),
        'ENABLE_COVERAGE': os.environ.get('ENABLE_COVERAGE', '0') == '1',
        'ENABLE_WAVEDUMP': os.environ.get('ENABLE_WAVEDUMP', '1') == '1',
    }

# Test collection hooks for APB HPET-specific organization
def pytest_collection_modifyitems(config, items):
    """Modify test collection to add APB HPET-specific markers"""
    for item in items:
        # Add markers based on test file patterns
        if "basic" in item.nodeid:
            item.add_marker(pytest.mark.basic)
        elif "medium" in item.nodeid:
            item.add_marker(pytest.mark.medium)
        elif "full" in item.nodeid:
            item.add_marker(pytest.mark.full)

        # Add feature-specific markers
        feature_markers = {
            'register': 'register_access',
            'timer': 'timer_operation',
            'counter': 'counter_operation',
            'interrupt': 'interrupt_handling',
            'periodic': 'periodic_mode',
            'oneshot': 'oneshot_mode',
            'cdc': 'clock_domain_crossing',
        }

        for feature, marker in feature_markers.items():
            if feature in item.nodeid.lower():
                item.add_marker(getattr(pytest.mark, marker))

# Register custom markers
def pytest_configure(config):
    """Register APB HPET-specific pytest markers and configure logging"""
    # Create logs directory if it doesn't exist
    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)

    # Configure log file for pytest itself
    config.option.log_file = os.path.join(log_dir, "pytest_apb_hpet.log")
    config.option.log_file_level = "DEBUG"

    # Enable console logging
    config.option.log_cli = True
    config.option.log_cli_level = "INFO"

    # Test level markers
    config.addinivalue_line("markers", "basic: Basic functionality tests")
    config.addinivalue_line("markers", "medium: Medium complexity tests")
    config.addinivalue_line("markers", "full: Full comprehensive tests")

    # Feature markers
    config.addinivalue_line("markers", "register_access: Register access tests")
    config.addinivalue_line("markers", "timer_operation: Timer operation tests")
    config.addinivalue_line("markers", "counter_operation: Counter operation tests")
    config.addinivalue_line("markers", "interrupt_handling: Interrupt handling tests")
    config.addinivalue_line("markers", "periodic_mode: Periodic timer mode tests")
    config.addinivalue_line("markers", "oneshot_mode: One-shot timer mode tests")
    config.addinivalue_line("markers", "clock_domain_crossing: CDC tests")

    # Configuration markers
    config.addinivalue_line("markers", "two_timer: 2-timer configuration tests")
    config.addinivalue_line("markers", "three_timer: 3-timer configuration tests")
    config.addinivalue_line("markers", "eight_timer: 8-timer configuration tests")

    # Performance markers
    config.addinivalue_line("markers", "stress: Stress testing")
    config.addinivalue_line("markers", "regression: Regression test suite")
