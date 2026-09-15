"""APB Crossbar test configuration for pytest.

The coverage/log boilerplate (log dir, coverage dir creation, log-file config,
marker registration, session-end coverage aggregation, scratch-dir ignore)
lives in ``bin/cov_utils/conftest_base.py`` -- the SAME shared base the val
areas, stream and rapids use. This file declares only the area-specific bits.

This replaced a hand-written conftest that re-implemented that boilerplate
locally, including a private ~175-line _aggregate_coverage/_generate_coverage_report
pair duplicating cov_utils.conftest_coverage.aggregate_all_coverage, and a local
get_coverage_compile_args whose docstring advertised
``from conftest import get_coverage_compile_args`` -- which nothing in the repo
ever did. The shared one is re-exported below instead.

Coverage: `COVERAGE=1` (line) / `COVERAGE_PROTOCOL=1` (protocol); aggregated at
session end by the shared base.
"""

import os
import sys

# Repo root + bin for the shared conftest base. env_python already exports these
# on PYTHONPATH -- added here too so a bare pytest invocation still resolves them.
_here = os.path.dirname(os.path.abspath(__file__))
_repo_root = os.path.abspath(os.path.join(_here, '../../../../..'))
for _p in (_repo_root, os.path.join(_repo_root, 'bin')):
    if _p in sys.path:
        sys.path.remove(_p)
    sys.path.insert(0, _p)

import pytest  # noqa: E402
from cov_utils.conftest_base import configure, sessionfinish, ignore_collect  # noqa: E402
from cov_utils.conftest_coverage import get_coverage_compile_args  # noqa: E402,F401 -- re-exported for test files

AREA_NAME = 'APB Crossbar'
LOG_BASENAME = 'pytest_apbx_xbar.log'
MARKERS = (
    'apbx_xbar: APB Crossbar tests',
    'basic: Basic functionality tests',
    'routing: Address routing tests',
    'arbitration: Arbitration tests',
    'stress: Stress testing',
    'coverage: Tests that collect coverage data',
    'protocol_coverage: Tests that collect protocol coverage',
)


def pytest_configure(config):
    configure(config, __file__, LOG_BASENAME, markers=MARKERS)


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    sessionfinish(__file__, AREA_NAME)


def pytest_ignore_collect(collection_path, config):
    return ignore_collect(collection_path)


def pytest_collection_modifyitems(config, items):
    """Modify test collection to add APB XBAR-specific markers"""
    for item in items:
        # Add markers based on test name patterns
        if "routing" in item.nodeid:
            item.add_marker(pytest.mark.routing)
        elif "arbitration" in item.nodeid:
            item.add_marker(pytest.mark.arbitration)
        elif "stress" in item.nodeid:
            item.add_marker(pytest.mark.stress)
        elif "basic" in item.nodeid:
            item.add_marker(pytest.mark.basic)


# NOTE: xbar_config, xbar_test_level and get_xbar_env_config used to live
# here. All three were dead -- nothing in the area ever requested them -- and
# xbar_test_level encoded a SECOND, conflicting level model (a module-scoped
# params fixture that would have tripled every test if anyone had used it,
# with its own transaction_count/timeout_factor table). Removed with the
# stamp so the reg_level_grid()/level_env() axis in the wrappers is the only
# level mechanism in this area.

# ----------------------------------------------------------------------
# Fixtures (kept local to this area)
# ----------------------------------------------------------------------
@pytest.fixture(scope="function")
def coverage_enabled():
    """Check if coverage collection is enabled."""
    return os.environ.get('COVERAGE', '0') == '1'


@pytest.fixture(scope="function")
def test_level():
    """Test level fixture - can be overridden by TEST_LEVEL environment variable.

    NOTE this is the fallback for a bare `pytest` run. Every wrapper in this area
    parametrizes `test_level` over reg_level_grid() and exports it with
    level_env(), and a parametrized argument takes precedence over a fixture of
    the same name -- so in a normal `make run-all-*` run this body does not
    execute.
    """
    return os.environ.get('TEST_LEVEL', 'gate')

# ----------------------------------------------------------------------
# NO REG_LEVEL -> TEST_LEVEL STAMP HERE. DELIBERATELY.
# ----------------------------------------------------------------------
# This area used to stamp os.environ['TEST_LEVEL'] = REG_LEVEL at import.
# cocotb_test.simulator.set_env copies every os.environ entry OVER the
# caller's extra_env, so the stamp beats any per-cell value a wrapper exports
# (TOOL-016). Here it was also inert: nothing in this area read TEST_LEVEL at
# all, so every cell ran one depth whatever the make target said.
#
# Every wrapper now parametrizes test_level over reg_level_grid() and exports
# it with level_env(), and each cocotb body picks its counts (and its
# timeout) from that. The fixture above stays as the fallback for a bare
# `pytest` run with no grid.
