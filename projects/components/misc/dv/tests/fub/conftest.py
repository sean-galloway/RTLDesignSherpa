"""
Misc FUB-Level Test Configuration for pytest

Configures the test environment for misc FUB-level unit tests.
Follows the established repository patterns (same as STREAM/RAPIDS).
"""

import os
import sys
import logging
import pytest


def pytest_configure(config):
    """Configure pytest environment for FUB tests."""
    misc_dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
    if misc_dv_path in sys.path:
        sys.path.remove(misc_dv_path)
    sys.path.insert(0, misc_dv_path)

    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)

    config.option.log_file = os.path.join(log_dir, "pytest_misc_fub.log")
    config.option.log_file_level = "DEBUG"
    config.option.log_cli = True
    config.option.log_cli_level = "INFO"


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    """Post-session hook."""
    logging.info("Misc FUB test session finished.")


def pytest_ignore_collect(collection_path, config):
    """Skip logs and build artifact directories."""
    path_str = str(collection_path)
    return 'logs' in path_str or 'local_sim_build' in path_str


@pytest.fixture(scope="function")
def test_level():
    """Test level fixture - gate/func/full from TEST_LEVEL env var."""
    return os.environ.get('TEST_LEVEL', 'gate')

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
