"""
Stream Characterization Test Configuration

Follows the established repository patterns (same as STREAM/RAPIDS).
"""

import os
import sys
import logging
import pytest


def pytest_configure(config):
    dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
    if dv_path in sys.path:
        sys.path.remove(dv_path)
    sys.path.insert(0, dv_path)

    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)
    config.option.log_file = os.path.join(log_dir, "pytest_stream_char.log")
    config.option.log_file_level = "DEBUG"
    config.option.log_cli = True
    config.option.log_cli_level = "INFO"


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    logging.info("Stream characterization test session finished.")


def pytest_ignore_collect(collection_path, config):
    path_str = str(collection_path)
    return 'logs' in path_str or 'local_sim_build' in path_str


@pytest.fixture(scope="function")
def test_level():
    return os.environ.get('TEST_LEVEL', 'gate')
