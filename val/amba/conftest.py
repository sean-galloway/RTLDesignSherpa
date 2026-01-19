"""
Validation Test Configuration for pytest - val/amba

Configures the test environment for RTL AMBA module tests.
Supports Verilator line coverage collection.

Coverage Features:
- Set COVERAGE=1 to enable Verilator line coverage collection
- Coverage reports are aggregated at session end
- Use `python bin/cov_utils/generate_coverage_report.py --dir val/amba` for reports

Environment Variables:
- COVERAGE=1: Enable coverage collection
- REG_LEVEL: GATE|FUNC|FULL - controls parameter combinations
- TEST_LEVEL: basic|medium|full - controls per-test depth
"""

import os
import sys
import logging
import glob
from datetime import datetime
import pytest

# Configure pytest to always collect logs
def pytest_configure(config):
    """Configure pytest with logging and coverage directories."""
    # Add bin/ to path for framework imports
    bin_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../bin'))
    if bin_path not in sys.path:
        sys.path.insert(0, bin_path)

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
    config.option.log_file = os.path.join(log_dir, "pytest_run.log")
    config.option.log_file_level = "DEBUG"

    # Enable console logging
    config.option.log_cli = True
    config.option.log_cli_level = "INFO"

    # Register coverage-related markers
    config.addinivalue_line("markers", "coverage: Tests that collect coverage data")


# Preserve all files regardless of test outcome
@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    """
    Called after whole test run finished, right before returning the exit status.
    Aggregates coverage data if coverage was enabled.
    """
    logging.info("val/amba test session finished. Preserving all logs and build artifacts.")

    # Aggregate coverage if enabled
    if os.environ.get('COVERAGE', '0') == '1':
        _aggregate_verilator_coverage()


def _aggregate_verilator_coverage():
    """Aggregate Verilator coverage.dat files from all test builds."""
    import subprocess
    import shutil

    base_dir = os.path.dirname(os.path.abspath(__file__))
    coverage_dir = os.path.join(base_dir, "coverage_data")
    merged_dir = os.path.join(coverage_dir, "merged")

    # Find all coverage.dat files in local_sim_build directories
    # Search ALL subdirectories since parameterized tests create dirs like
    # test_counter_bin_w5_max10_basic_GATE/ not just test_counter_bin/
    dat_files = []
    sim_build_root = os.path.join(base_dir, "local_sim_build")
    if os.path.isdir(sim_build_root):
        for root, dirs, files in os.walk(sim_build_root):
            if "coverage.dat" in files:
                dat_files.append(os.path.join(root, "coverage.dat"))

    if not dat_files:
        logging.info("No coverage.dat files found to aggregate")
        return

    logging.info(f"Found {len(dat_files)} coverage.dat files to aggregate")

    # Merge coverage files using verilator_coverage
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    merged_file = os.path.join(merged_dir, f"merged_coverage_{timestamp}.dat")
    latest_file = os.path.join(merged_dir, "latest_merged_coverage.dat")

    try:
        cmd = ['verilator_coverage', '--write', merged_file] + dat_files
        result = subprocess.run(cmd, capture_output=True, text=True)
        if result.returncode == 0:
            logging.info(f"Coverage merged: {merged_file}")
            # Also save as latest
            shutil.copy(merged_file, latest_file)
        else:
            logging.warning(f"Coverage merge failed: {result.stderr}")
    except FileNotFoundError:
        logging.warning("verilator_coverage not found - coverage aggregation skipped")
    except Exception as e:
        logging.warning(f"Coverage aggregation error: {e}")


# Disable automatic test collection in special directories
def pytest_ignore_collect(collection_path, config):
    path_str = str(collection_path)
    return ('logs' in path_str or 'coverage_data' in path_str or
            'local_sim_build' in path_str)


# Test level fixture - provides test complexity level
@pytest.fixture(scope="function")
def test_level():
    """Test level fixture - can be overridden by TEST_LEVEL environment variable."""
    return os.environ.get('TEST_LEVEL', 'basic')


# Coverage fixtures
@pytest.fixture(scope="function")
def coverage_enabled():
    """Check if coverage collection is enabled."""
    return os.environ.get('COVERAGE', '0') == '1'


# Helper functions that tests can import
def get_coverage_compile_args():
    """
    Get Verilator compile arguments for coverage collection.

    Use in test pytest wrapper:
        from conftest import get_coverage_compile_args
        compile_args.extend(get_coverage_compile_args())
    """
    if os.environ.get('COVERAGE', '0') != '1':
        return []

    return [
        '--coverage',
        '--coverage-line',
        '--coverage-toggle',
        '--coverage-underscore',
    ]
