"""ALU-INFER test configuration for pytest.

Boilerplate (log dir, coverage aggregation, marker registration) lives in
``bin/cov_utils/conftest_base.py`` -- the shared base the other component
areas use. This file declares only the area-specific bits.
"""

import os
import sys

_here = os.path.dirname(os.path.abspath(__file__))
_repo_root = os.path.abspath(os.path.join(_here, '../../../../../..'))
for _p in (_repo_root, os.path.join(_repo_root, 'bin')):
    if _p in sys.path:
        sys.path.remove(_p)
    sys.path.insert(0, _p)

import pytest  # noqa: E402
from cov_utils.conftest_base import configure, sessionfinish, ignore_collect  # noqa: E402
from cov_utils.conftest_coverage import get_coverage_compile_args  # noqa: E402,F401 -- re-exported for test files

AREA_NAME = 'ALU-INFER'
LOG_BASENAME = 'pytest_alu_infer.log'
MARKERS = (
    'alu_infer: ALU-INFER block tests',
    'basic: Basic functionality tests',
    'coverage: Tests that collect coverage data',
)


def pytest_configure(config):
    configure(config, __file__, LOG_BASENAME, markers=MARKERS)


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    sessionfinish(__file__, AREA_NAME)


def pytest_ignore_collect(collection_path, config):
    return ignore_collect(collection_path)


@pytest.fixture(scope="function")
def coverage_enabled():
    """Check if coverage collection is enabled."""
    return os.environ.get('COVERAGE', '0') == '1'


@pytest.fixture(scope="function")
def test_level():
    """Fallback test level for a bare `pytest` run."""
    return os.environ.get('TEST_LEVEL', 'gate')
