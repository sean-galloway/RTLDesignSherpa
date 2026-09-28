"""RAPIDS FUB-Beats test configuration for pytest.

The coverage/log boilerplate (log dir, coverage dir creation, log-file config,
marker registration, session-end coverage aggregation, scratch-dir ignore)
lives in ``bin/cov_utils/conftest_base.py`` -- the SAME shared base the val
areas, stream, bridge and converters use. This file declares only the
RAPIDS-FUB-Beats-specific bits.

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

AREA_NAME = 'RAPIDS FUB-Beats'
LOG_BASENAME = 'pytest_rapids_fub_beats.log'
MARKERS = (
    'coverage: Tests that collect coverage data',
    'protocol_coverage: Tests that collect protocol coverage',
    'fub: FUB-level tests, applied by this area',
    'fub_beats: FUB-level beats architecture tests',
    'scheduler: Scheduler tests',
    'descriptor_engine: Descriptor-engine tests',
    'beats_alloc_ctrl: Beats alloc-ctrl tests',
    'beats_drain_ctrl: Beats drain-ctrl tests',
    'beats_latency_bridge: Beats latency-bridge tests',
    'stress: Stress testing',
    'error: Error injection tests',
    'integration: Integration tests',
    'macro: Macro-level tests, applied by some fub_beats tests',
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


# The REG_LEVEL -> TEST_LEVEL stamp that used to live here is gone (tooling
# BUG-004, was TOOL-016, 2026-09-27). cocotb_test copies every os.environ
# entry over a wrapper's extra_env, so stamping TEST_LEVEL at conftest import
# made every cell of a run take the process value: the REG_LEVEL grid existed
# in collection only. Each wrapper now exports its own cell's level through
# TBClasses.shared.test_levels.level_env and the TBs read depth from
# rapids_levels.PROFILE. Nothing may put TEST_LEVEL back into os.environ.
