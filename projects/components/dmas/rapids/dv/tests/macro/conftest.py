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

# ----------------------------------------------------------------------
# REG_LEVEL -> TEST_LEVEL bridge
# ----------------------------------------------------------------------
# make/tests.mk drives the regression level through REG_LEVEL; this area's test
# modules read TEST_LEVEL, and most read it at MODULE IMPORT time. conftest is
# imported before any test module, so setting it here is early enough.
#
# WITHOUT THIS BRIDGE THE MAKEFILE CONVERGENCE SILENTLY REDUCES COVERAGE: the
# 4-line area Makefile sets REG_LEVEL=full, nothing reads it, TEST_LEVEL falls
# back to its default, and `make run-all-full-parallel` quietly runs a smaller
# matrix while still reporting "passed". Measured on pumice fub during this
# conversion: 91 tests -> 79.
#
# REG_LEVEL wins over TEST_LEVEL, matching stream's conftest: the make target
# you typed is more explicit than an inherited environment variable.
_reg_level = os.environ.get('REG_LEVEL')
if _reg_level:
    os.environ['TEST_LEVEL'] = _reg_level.upper()
