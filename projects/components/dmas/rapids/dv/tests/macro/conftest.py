"""
RAPIDS Macro-Level Test Configuration for pytest

Configures the test environment for RAPIDS macro-level integration tests.
Follows the established repository patterns.
"""

import os
import sys
import logging
import pytest

# Configure pytest to always collect logs
def pytest_configure(config):
    # Add RAPIDS DV directory to path BEFORE pytest imports test modules
    # CRITICAL: Must be at position 0, even if already in sys.path from PYTHONPATH
    rapids_dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))

    # Remove if already present (from PYTHONPATH), then insert at position 0
    if rapids_dv_path in sys.path:
        sys.path.remove(rapids_dv_path)
    sys.path.insert(0, rapids_dv_path)

    # Create logs directory if it doesn't exist
    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)

    # Configure log file for pytest itself
    config.option.log_file = os.path.join(log_dir, "pytest_macro.log")
    config.option.log_file_level = "DEBUG"

    # Enable console logging
    config.option.log_cli = True
    config.option.log_cli_level = "INFO"

# Preserve all files regardless of test outcome
@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    """
    Called after whole test run finished, right before returning the exit status.
    """
    logging.info("RAPIDS macro test session finished. Preserving all logs and build artifacts.")

# Disable automatic test collection in the logs directory if it exists
def pytest_ignore_collect(collection_path, config):
    return 'logs' in str(collection_path)
