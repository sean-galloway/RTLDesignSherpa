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
# REG_LEVEL -> TEST_LEVEL: deliberately NOT bridged here
# ----------------------------------------------------------------------
# This area used to stamp os.environ['TEST_LEVEL'] = REG_LEVEL at import.
# cocotb_test.simulator.set_env copies every os.environ entry OVER the
# caller's extra_env, so that stamp beat the per-cell value a wrapper passed.
# test_dma_address_gen already exported a per-cell TEST_LEVEL and its TB has a
# real gate/func/full table; the stamp overrode both, and all 48 cells ran at
# one depth while the run reported three levels (TOOL-016).
#
# Every wrapper in this area now parametrizes test_level over
# reg_level_grid() and exports it with level_env(), so the stamp is gone. The
# fixture below stays as the fallback for a bare `pytest` invocation with no
# grid, where TEST_LEVEL from the environment is the only signal.
