"""Timing Characterization Top-level test configuration for pytest.

The coverage/log boilerplate (log dir, coverage dir creation, log-file config,
marker registration, session-end coverage aggregation, scratch-dir ignore)
lives in ``bin/cov_utils/conftest_base.py`` -- the SAME shared base the val
areas, stream, rapids, apbx-xbar and retro_legacy_blocks use. This file
declares only the area-specific bits.

Coverage: `COVERAGE=1` (line) / `COVERAGE_PROTOCOL=1` (protocol); aggregated at
session end by the shared base.
"""

import os
import sys

# Repo root + bin for the shared conftest base; the timing_characterization dv
# dir so `from tbclasses.timing_char_tb import ...` resolves. The dotted
# package form cannot be used here: `asic-trials` contains a hyphen and is not
# a valid Python package name, which is why the 2026-09-08 move could not
# simply rewrite the import path. Same arrangement as pumice.
_here = os.path.dirname(os.path.abspath(__file__))
_repo_root = os.path.abspath(os.path.join(_here, '../../../../../..'))
for _p in (_repo_root, os.path.join(_repo_root, 'bin')):
    if _p in sys.path:
        sys.path.remove(_p)
    sys.path.insert(0, _p)
_tc_dv = os.path.abspath(os.path.join(_here, '../..'))
if _tc_dv in sys.path:
    sys.path.remove(_tc_dv)
sys.path.insert(0, _tc_dv)

import pytest  # noqa: E402
from cov_utils.conftest_base import configure, sessionfinish, ignore_collect  # noqa: E402
from cov_utils.conftest_coverage import get_coverage_compile_args  # noqa: E402,F401 -- re-exported for test files

AREA_NAME = 'Timing Characterization Top'
LOG_BASENAME = 'pytest_timing_char_top.log'
MARKERS = (
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


# ----------------------------------------------------------------------
# Fixtures (kept local to this area)
# ----------------------------------------------------------------------
@pytest.fixture(scope="function")
def test_level():
    """Test level: REG_LEVEL (GATE/FUNC/FULL, set by make/tests.mk) wins so the
    4-line area Makefiles drive it; TEST_LEVEL is the manual fallback.

    THIS AREA IS DIFFERENT FROM THE OTHERS AND THE DIFFERENCE MATTERS. Elsewhere
    the wrappers parametrize `test_level` over reg_level_grid() and this fixture
    is an inert fallback. Here the wrappers take `test_level` as a real fixture
    argument (measured: 5+ signatures) and nothing uses reg_level_grid(), so
    this body IS the depth mechanism. It previously read TEST_LEVEL only, while
    make/tests.mk drives REG_LEVEL -- so `make run-all-full` handed the tests
    'gate'. Collection is not level-gated either way (fub 34 / top 11 at every
    level), which is exactly why the loss was silent.
    """
    reg = os.environ.get('REG_LEVEL')
    if reg:
        return {'GATE': 'gate', 'FUNC': 'func', 'FULL': 'full'}.get(reg.upper(), reg.lower())
    return os.environ.get('TEST_LEVEL', 'gate')


@pytest.fixture(scope="function")
def coverage_enabled():
    """Whether coverage collection is enabled for this run."""
    return os.environ.get('COVERAGE', '0') == '1'
