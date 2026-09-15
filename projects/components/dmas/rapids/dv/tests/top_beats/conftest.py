"""RAPIDS Top-Beats test configuration for pytest.

The coverage/log boilerplate (log dir, coverage dir creation, log-file config,
marker registration, session-end coverage aggregation, scratch-dir ignore)
lives in ``bin/cov_utils/conftest_base.py`` -- the SAME shared base the val
areas, stream, bridge and converters use. This file declares only the
RAPIDS-Top-Beats-specific bits.

This replaced a hand-written conftest that re-implemented that boilerplate
locally. fub_beats and macro_beats had each grown a ~175-line private
_aggregate_coverage/_generate_coverage_report pair, byte-identical to one
another apart from five title strings, duplicating
cov_utils.conftest_coverage.aggregate_all_coverage.

MARKERS are the union of what this area's tests actually apply (measured) and
what the previous conftest registered. The two had drifted: fub_beats tests
apply `fub` 34 times and never `fub_beats`, while the old conftest registered
`fub_beats` and not `fub`; macro and top_beats registered nothing at all.

Coverage: `COVERAGE=1` (line) / `COVERAGE_PROTOCOL=1` (protocol); aggregated at
session end by the shared base.
"""

import os
import sys

# Repo root + bin for the shared conftest base; the RAPIDS dv dir for the area's
# own imports (rapids_coverage, tbclasses). env_python already exports these on
# PYTHONPATH -- added here too so a bare pytest invocation still resolves them.
# NOTE the tests import fully-qualified
# (projects.components.dmas.rapids.dv.tbclasses.*), which resolves from the REPO
# ROOT -- not from rapids/ or rapids/dv/. The old conftests inserted one of those
# two instead, inconsistently (fub went up three levels, the rest up two); neither
# was what made the imports work.
_here = os.path.dirname(os.path.abspath(__file__))
_repo_root = os.path.abspath(os.path.join(_here, '../../../../../../..'))
for _p in (_repo_root, os.path.join(_repo_root, 'bin')):
    if _p in sys.path:
        sys.path.remove(_p)
    sys.path.insert(0, _p)
_rapids_dv = os.path.abspath(os.path.join(_here, '../..'))
if _rapids_dv in sys.path:
    sys.path.remove(_rapids_dv)
sys.path.insert(0, _rapids_dv)

import pytest  # noqa: E402
from cov_utils.conftest_base import configure, sessionfinish, ignore_collect  # noqa: E402
from cov_utils.conftest_coverage import get_coverage_compile_args  # noqa: E402,F401 -- re-exported for test files

AREA_NAME = 'RAPIDS Top-Beats'
LOG_BASENAME = 'pytest_rapids_top_beats.log'
MARKERS = (
    'coverage: Tests that collect coverage data',
    'protocol_coverage: Tests that collect protocol coverage',
    'top_beats: Top-level beats architecture tests',
    'rapids_beats_top: rapids_beats_top tests',
    'rapids_core_beats: rapids_core_beats tests',
)


def pytest_configure(config):
    configure(config, __file__, LOG_BASENAME, markers=MARKERS)


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    sessionfinish(__file__, AREA_NAME)


def pytest_ignore_collect(collection_path, config):
    return ignore_collect(collection_path)


# ----------------------------------------------------------------------
# RAPIDS fixtures (kept local to the area)
# ----------------------------------------------------------------------
@pytest.fixture(scope="function")
def test_level():
    """Test level: REG_LEVEL (GATE/FUNC/FULL, set by make/tests.mk) wins so the
    4-line area Makefiles drive it; TEST_LEVEL is the manual fallback."""
    reg = os.environ.get('REG_LEVEL')
    if reg:
        return {'GATE': 'gate', 'FUNC': 'func', 'FULL': 'full'}.get(reg.upper(), reg.lower())
    return os.environ.get('TEST_LEVEL', 'gate')


@pytest.fixture(scope="function")
def coverage_enabled():
    """Whether coverage collection is enabled for this run."""
    return os.environ.get('COVERAGE', '0') == '1'


@pytest.fixture(scope="function")
def coverage_config():
    """RAPIDS functional-coverage config (rapids_coverage package)."""
    from projects.components.dmas.rapids.dv.rapids_coverage.coverage_config import (
        RapidsCoverageConfig,
    )
    return RapidsCoverageConfig.from_environment()


# ----------------------------------------------------------------------
# REG_LEVEL -> TEST_LEVEL bridge
# ----------------------------------------------------------------------
# make/tests.mk drives the level through REG_LEVEL. The test_level fixture above
# already prefers REG_LEVEL, so this stamp is belt-and-braces for any consumer
# reading the env var directly rather than taking the fixture. Measured
# 2026-09-14: no rapids test module references TEST_LEVEL, and the only two files
# that do (conftest_scheduler_beats.py, conftest_descriptor_engine_beats.py) are
# never imported -- so it is vestigial. KEPT rather than removed: it costs
# nothing, and deleting it is a behaviour change unrelated to converting the
# conftest structure.
_reg_level = os.environ.get('REG_LEVEL')
if _reg_level:
    os.environ['TEST_LEVEL'] = _reg_level.upper()
