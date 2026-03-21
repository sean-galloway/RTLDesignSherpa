"""
Timing Characterization FUB-Level Test Configuration for pytest

Configures the test environment for timing characterization unit tests.
"""

import os
import sys
import logging
import pytest


def pytest_configure(config):
    # Add timing_characterization DV directory to path
    tc_dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))

    if tc_dv_path in sys.path:
        sys.path.remove(tc_dv_path)
    sys.path.insert(0, tc_dv_path)

    # Create logs directory
    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)

    # Configure log file
    config.option.log_file = os.path.join(log_dir, "pytest_timing_char_fub.log")
    config.option.log_file_level = "DEBUG"
    config.option.log_cli = True
    config.option.log_cli_level = "INFO"


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    """Called after whole test run finished."""
    logging.info("Timing characterization FUB test session finished.")


def pytest_ignore_collect(collection_path, config):
    path_str = str(collection_path)
    return 'logs' in path_str or 'local_sim_build' in path_str


@pytest.fixture(scope="function")
def test_level():
    """Test level fixture."""
    return os.environ.get('TEST_LEVEL', 'gate')
