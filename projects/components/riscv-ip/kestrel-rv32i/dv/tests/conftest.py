# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: conftest
# Purpose: pytest configuration for kestrel-rv32i dv/tests.
#
# Wires the shared cov_utils conftest base (bin/cov_utils/conftest_base.py) for
# log/coverage directory setup, marker registration, local_sim_build ignore, and
# session-end Verilator coverage aggregation.  Coverage is collected when
# COVERAGE=1 is set in the environment; the shared base also centrally injects
# Verilator --coverage flags into cocotb_test.simulator.run so individual test
# files do not need to add them.
#
# Coverage: `COVERAGE=1` (Verilator line/toggle), aggregated at session end via
# the shared base.  Report: `make coverage-report`.
# Env: `REG_LEVEL` (GATE|FUNC|FULL, drives parametrization in the tests) /
# `TEST_LEVEL` (per-test depth).  The kestrel test files pass Verilator-specific
# compile args (--trace-depth, --timescale, etc.) without selecting a simulator,
# so default to Verilator unless the caller already set SIM.

import os
import sys

# Default simulator for this area.  The test wrappers use Verilator-specific
# compile arguments; leaving cocotb_test's default (iverilog) makes even a
# non-coverage run fail with "invalid option -- '-'."  Respect an explicit SIM.
os.environ.setdefault('SIM', 'verilator')

_AREA_DIR = os.path.dirname(os.path.abspath(__file__))


def _repo_bin(start):
    """The repo's bin/, found by walking up -- not a fixed relative path."""
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

AREA_NAME = 'kestrel-rv32i'
LOG_BASENAME = 'pytest_run.log'
MARKERS = ('coverage: Tests that collect coverage data',)


def pytest_configure(config):
    configure(config, __file__, LOG_BASENAME, markers=MARKERS)


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    sessionfinish(__file__, AREA_NAME)


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
