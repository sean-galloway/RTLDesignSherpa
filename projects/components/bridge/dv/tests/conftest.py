"""Validation test configuration for pytest -- projects/components/bridge/dv/tests.

The area name is DERIVED from this file's location (the component directory
three levels up), never typed, for the same reason val/<area> derives it:
a copied conftest that announces the wrong area cannot drift like that.

Coverage/log boilerplate (log dir, coverage collection + session-end
aggregation, scratch-dir ignore) lives in ``bin/cov_utils/conftest_base.py``
-- the SAME shared base every val area uses. This file is the val/common
conftest plus the two path entries a Pattern B area needs, and nothing else.
It used to carry 100 more lines: parametrization fixtures for an RTL-
parameterised bridge that has never existed (the fabrics are generated per
config), a marker auto-tagger nothing selected on, and a REG_LEVEL ->
os.environ['TEST_LEVEL'] stamp that overrode every per-cell TEST_LEVEL the
wrappers export (cocotb_test copies os.environ over extra_env) -- the first
leveled FULL run executed all 216 cells at full depth because of it.

Coverage: `COVERAGE=1` (Verilator line/toggle), aggregated at session end via
the shared base. Report: `make coverage-report`. Env: `REG_LEVEL` (GATE|FUNC|
FULL, drives the grid in each wrapper's generate_bridge_levels) / `TEST_LEVEL`
(per-cell depth, exported by the wrapper, read by the TB). Waves: `WAVES=1`
(the `-waves` make targets), honoured through TBClasses.shared.utilities.
get_wave_config in every wrapper.
"""

import os
import sys

_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_TESTS_DIR, '../../../../..'))
AREA = os.path.basename(os.path.abspath(os.path.join(_TESTS_DIR, '../..')))  # 'bridge' -- derived
sys.path.insert(0, os.path.join(_REPO_ROOT, 'bin'))
# Pattern B: tests and TB classes import `projects.components.bridge...`, so
# the repo root must resolve at collection time too.
sys.path.insert(0, _REPO_ROOT)
# This directory too: the _mon tests do `from monitor_stress_common import ...`,
# a sibling module. pytest only prepends a test file's own directory when it is
# invoked from inside it, so collecting from the repo root used to fail with
# ModuleNotFoundError on every _mon test.
sys.path.insert(0, _TESTS_DIR)

import pytest  # noqa: E402
from cov_utils.conftest_base import configure, sessionfinish, ignore_collect  # noqa: E402
from cov_utils.conftest_coverage import get_coverage_compile_args  # noqa: E402,F401 — re-exported for test wrappers

LOG_BASENAME = 'pytest_run.log'
MARKERS = ('coverage: Tests that collect coverage data',)


def pytest_configure(config):
    configure(config, __file__, LOG_BASENAME, markers=MARKERS)


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    sessionfinish(__file__, AREA)


def pytest_ignore_collect(collection_path, config):
    return ignore_collect(collection_path)


@pytest.fixture(scope="function")
def test_level():
    """Test level (TEST_LEVEL override; REG_LEVEL drives parametrization in tests)."""
    return os.environ.get('TEST_LEVEL', 'gate').lower()


@pytest.fixture(scope="function")
def coverage_enabled():
    """Whether coverage collection is enabled for this run."""
    return os.environ.get('COVERAGE', '0') == '1'
