"""STREAM FUB-level test configuration for pytest.

The coverage/log boilerplate (log dir, coverage aggregation, scratch-dir ignore)
lives in ``bin/cov_utils/conftest_base.py`` — the SAME shared base the bridge and
converters conftests use. This file declares only the STREAM-specific bits.

Coverage: `COVERAGE=1` (line) / `COVERAGE_PROTOCOL=1` (protocol); aggregated at
session end. Report: `make coverage-report` (bin/cov_utils/merge_testlevel_coverage.py).
"""

import os
import sys

# Repo root + bin on path for the shared conftest base; the STREAM dv dir for the
# area's own imports (stream_coverage, tbclasses). env_python already exports these
# on PYTHONPATH — added here too so a bare pytest invocation still resolves them.
_here = os.path.dirname(os.path.abspath(__file__))
_repo_root = os.path.abspath(os.path.join(_here, '../../../../../../..'))
sys.path.insert(0, _repo_root)
sys.path.insert(0, os.path.join(_repo_root, 'bin'))
_stream_dv = os.path.abspath(os.path.join(_here, '../..'))
if _stream_dv in sys.path:
    sys.path.remove(_stream_dv)
sys.path.insert(0, _stream_dv)

import pytest  # noqa: E402
from cov_utils.conftest_base import configure, sessionfinish, ignore_collect  # noqa: E402
from cov_utils.conftest_coverage import get_coverage_compile_args  # noqa: E402,F401 — re-exported for test files

AREA_NAME = 'STREAM FUB'
LOG_BASENAME = 'pytest_stream_fub.log'
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
# STREAM-specific fixtures (kept local to this area).
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
    """STREAM functional-coverage config (stream_coverage package)."""
    from projects.components.dmas.stream.dv.stream_coverage import CoverageConfig
    return CoverageConfig.from_environment()
