"""Validation test configuration for pytest -- jet-mesi-l1/dv/tests.

Delegates coverage/log boilerplate to cov_utils.conftest_base, the same
shared base used by val/ and other project areas.  This file exists so
COVERAGE=1 runs inject Verilator coverage flags and aggregate per-test
coverage data under dv/tests/coverage_data/.
"""

import os
import sys

_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_TESTS_DIR, '../../../../../..'))
AREA = 'jet'
sys.path.insert(0, os.path.join(_REPO_ROOT, 'bin'))
sys.path.insert(0, _REPO_ROOT)
sys.path.insert(0, os.path.join(_TESTS_DIR, os.pardir, 'tbclasses'))
sys.path.insert(0, _TESTS_DIR)

# Jet reuses the shared l1_* TB machinery and golden model (common-ip);
# make them importable by jet tests without copying.
sys.path.insert(0, os.path.join(_REPO_ROOT, 'projects', 'components', 'cache-ip', 'common-ip', 'dv', 'tbclasses'))
sys.path.insert(0, os.path.join(_REPO_ROOT, 'projects', 'components', 'cache-ip', 'common-ip', 'dv', 'golden'))

import pytest  # noqa: E402
from cov_utils.conftest_base import configure, sessionfinish, ignore_collect  # noqa: E402
from cov_utils.conftest_coverage import get_coverage_compile_args  # noqa: E402,F401

LOG_BASENAME = 'pytest_run.log'
MARKERS = ('coverage: Tests that collect coverage data',)

# Jet inherits amber's combinational datapath waiver for coverage runs.
try:
    import cocotb_test.simulator as _cts
    _orig_run = _cts.run

    def _jet_run(*args, **kwargs):
        if os.environ.get('COVERAGE', '0') == '1':
            compile_args = list(kwargs.get('compile_args') or [])
            if '-Wno-UNOPTFLAT' not in compile_args:
                compile_args.append('-Wno-UNOPTFLAT')
            kwargs['compile_args'] = compile_args
        return _orig_run(*args, **kwargs)

    _cts.run = _jet_run
except Exception:
    pass


def pytest_configure(config):
    configure(config, __file__, LOG_BASENAME, markers=MARKERS)


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    sessionfinish(__file__, AREA)


def pytest_ignore_collect(collection_path, config):
    return ignore_collect(collection_path)


@pytest.fixture(scope="function")
def test_level():
    return os.environ.get('TEST_LEVEL', 'gate').lower()


@pytest.fixture(scope="function")
def coverage_enabled():
    return os.environ.get('COVERAGE', '0') == '1'
