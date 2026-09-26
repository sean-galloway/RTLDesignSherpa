"""Validation test configuration for pytest — val/<area>.

The area name is DERIVED from this file's directory, never typed: val/common was
once copied to val/math and kept announcing "val/common" / pointing reports at
--dir val/common while running math. A derived name cannot drift like that.

Coverage/log boilerplate (log dir, coverage collection + session-end aggregation,
scratch-dir ignore) lives in ``bin/cov_utils/conftest_base.py`` — the SAME shared
base bridge, converters, and the stream conftests use. This file is identical
across every val area; it declares only the area-agnostic bits.

Coverage: `COVERAGE=1` (Verilator line/toggle), aggregated at session end via the
shared base. Report: `make coverage-report`. Env: `REG_LEVEL` (GATE|FUNC|FULL,
drives parametrization in the tests) / `TEST_LEVEL` (per-test depth).
"""

import os
import sys

_AREA_DIR = os.path.dirname(os.path.abspath(__file__))
AREA = os.path.basename(_AREA_DIR)   # 'common' / 'cdc' / 'amba' / 'monitor-lite' — derived


def _repo_bin(start):
    """The repo's bin/, found by walking up -- not a fixed '../../bin'.

    A sub-area (val/amba/monitor-lite, 2026-09-25) sits one level deeper than
    the four original areas, and a hard-coded depth pointed it at val/bin.
    """
    d = start
    while True:
        cand = os.path.join(d, 'bin', 'cov_utils')
        if os.path.isdir(cand):
            return os.path.join(d, 'bin')
        parent = os.path.dirname(d)
        if parent == d:
            raise RuntimeError(f'no bin/cov_utils above {start}')
        d = parent


sys.path.insert(0, _repo_bin(_AREA_DIR))

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
