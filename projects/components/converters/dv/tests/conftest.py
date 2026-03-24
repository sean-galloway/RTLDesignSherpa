"""
Converters Validation Test Configuration for pytest

Configures the test environment for AXI4 width converters and protocol converters,
following the established repository patterns.

Coverage Features:
- Set COVERAGE=1 to enable code coverage collection
- Set COVERAGE_PROTOCOL=1 to enable protocol coverage collection
- Coverage reports are aggregated at session end
"""

import os
import sys
import logging
import pytest

# Add repository paths before any test imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, repo_root)
sys.path.insert(0, os.path.join(repo_root, 'bin'))


def get_coverage_compile_args():
    """Get Verilator compile arguments for coverage collection.

    Usage in test files:
        from conftest import get_coverage_compile_args
        compile_args.extend(get_coverage_compile_args())

    Enable coverage by setting COVERAGE=1 environment variable.
    """
    if os.environ.get('COVERAGE', '0') != '1':
        return []
    return [
        '--coverage',
        '--coverage-line',
        '--coverage-toggle',
        '--coverage-underscore',
    ]


def pytest_configure(config):
    """Configure pytest for Converters testing"""
    # Create logs directory if it doesn't exist
    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)

    # Create coverage directory if coverage is enabled
    if os.environ.get('COVERAGE', '0') == '1':
        coverage_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "coverage_data")
        os.makedirs(os.path.join(coverage_dir, "per_test"), exist_ok=True)
        os.makedirs(os.path.join(coverage_dir, "merged"), exist_ok=True)
        os.makedirs(os.path.join(coverage_dir, "reports"), exist_ok=True)
        logging.info(f"Coverage enabled. Data will be stored in: {coverage_dir}")

    # Configure log file for pytest itself
    config.option.log_file = os.path.join(log_dir, "pytest_converters.log")
    config.option.log_file_level = "DEBUG"

    # Enable console logging
    config.option.log_cli = True
    config.option.log_cli_level = "INFO"

    # Register Converter-specific pytest markers
    config.addinivalue_line("markers", "converter: Converter tests")
    config.addinivalue_line("markers", "width: Width converter tests")
    config.addinivalue_line("markers", "protocol: Protocol converter tests")
    config.addinivalue_line("markers", "upsize: Upsizing tests")
    config.addinivalue_line("markers", "downsize: Downsizing tests")
    config.addinivalue_line("markers", "axi4: AXI4 tests")
    config.addinivalue_line("markers", "axil4: AXI4-Lite tests")
    config.addinivalue_line("markers", "apb: APB tests")
    config.addinivalue_line("markers", "coverage: Tests that collect coverage data")
    config.addinivalue_line("markers", "protocol_coverage: Tests that collect protocol coverage")


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    """Called after whole test run finished"""
    logging.info("Converters test session finished. Preserving all logs and build artifacts.")

    # Aggregate coverage if enabled
    if os.environ.get('COVERAGE', '0') == '1':
        _aggregate_coverage()


def _aggregate_coverage():
    """Aggregate all per-test coverage data into a merged report.

    Delegates to the shared coverage helper which correctly:
    - Uses MAX hits (not SUM) for protocol coverage deduplication
    - Merges Verilator .dat files via verilator_coverage --write
    - Generates a Markdown report with coverage gaps
    """
    from cov_utils.conftest_coverage import aggregate_all_coverage

    base_dir = os.path.dirname(os.path.abspath(__file__))
    aggregate_all_coverage(base_dir, 'Converters')


def pytest_ignore_collect(collection_path, config):
    """Disable automatic test collection in logs and coverage directories"""
    path_str = str(collection_path)
    return 'logs' in path_str or 'coverage_data' in path_str


# Converter-specific parametrization fixtures
@pytest.fixture(scope="module", params=[
    # (src_width, dst_width, description)
    (32, 64, "32->64 upsize"),
    (64, 128, "64->128 upsize"),
    (128, 256, "128->256 upsize"),
    (64, 32, "64->32 downsize"),
    (128, 64, "128->64 downsize"),
    (256, 128, "256->128 downsize"),
])
def width_config(request):
    """Width converter configuration parameters"""
    src_width, dst_width, description = request.param
    return {
        'SRC_WIDTH': src_width,
        'DST_WIDTH': dst_width,
        'description': description,
        'is_upsize': dst_width > src_width,
    }


@pytest.fixture(scope="module", params=[
    # Test levels: (level, transaction_count, timeout_factor)
    ('gate', 10, 1.0),
    ('func', 50, 1.5),
    ('full', 200, 2.0),
])
def converter_test_level(request):
    """Converter test level configuration"""
    level, transaction_count, timeout_factor = request.param

    # Override from environment if specified
    env_level = os.environ.get('TEST_LEVEL', level).lower()
    if env_level in ['gate', 'func', 'full']:
        level = env_level

    return {
        'level': level,
        'transaction_count': transaction_count,
        'timeout_factor': timeout_factor
    }


def get_converter_env_config():
    """Get Converter configuration from environment variables"""
    return {
        'SRC_WIDTH': int(os.environ.get('CONV_SRC_WIDTH', '64')),
        'DST_WIDTH': int(os.environ.get('CONV_DST_WIDTH', '128')),
        'ADDR_WIDTH': int(os.environ.get('CONV_ADDR_WIDTH', '32')),
        'ID_WIDTH': int(os.environ.get('CONV_ID_WIDTH', '4')),
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', 'gate').lower(),
        'ENABLE_WAVEDUMP': os.environ.get('ENABLE_WAVEDUMP', '1') == '1',
    }


def pytest_collection_modifyitems(config, items):
    """Modify test collection to add Converter-specific markers"""
    for item in items:
        # Add markers based on test name patterns
        if "upsize" in item.nodeid:
            item.add_marker(pytest.mark.upsize)
        elif "downsize" in item.nodeid:
            item.add_marker(pytest.mark.downsize)

        if "axi4_to_axil4" in item.nodeid or "axil4_to_axi4" in item.nodeid:
            item.add_marker(pytest.mark.protocol)
        elif "dwidth" in item.nodeid:
            item.add_marker(pytest.mark.width)


# Coverage fixtures
@pytest.fixture(scope="function")
def coverage_enabled():
    """Check if coverage collection is enabled."""
    return os.environ.get('COVERAGE', '0') == '1'


@pytest.fixture(scope="function")
def test_level():
    """Test level fixture - can be overridden by TEST_LEVEL environment variable"""
    return os.environ.get('TEST_LEVEL', 'gate')
