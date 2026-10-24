"""STREAM-g FUB test configuration for pytest (stream-g, stream TASK-020).

fub/conftest.py with this area's names and markers.
"""

import os
import sys

# Repo root + bin for the shared conftest base; the STREAM dv dir for the
# area's own imports (stream_coverage, tbclasses). env_python already exports
# these on PYTHONPATH -- added here too so a bare pytest invocation still
# resolves them. The tests import fully-qualified
# (projects.components.dma_ip.stream.dv.tbclasses.*), which resolves from the
# REPO ROOT.
_here = os.path.dirname(os.path.abspath(__file__))
_repo_root = os.path.abspath(os.path.join(_here, '../../../../../../..'))
for _p in (_repo_root, os.path.join(_repo_root, 'bin')):
    if _p in sys.path:
        sys.path.remove(_p)
    sys.path.insert(0, _p)
_stream_dv = os.path.abspath(os.path.join(_here, '../..'))
if _stream_dv in sys.path:
    sys.path.remove(_stream_dv)
sys.path.insert(0, _stream_dv)

import pytest  # noqa: E402
from cov_utils.conftest_base import configure, sessionfinish, ignore_collect  # noqa: E402
from cov_utils.conftest_coverage import get_coverage_compile_args  # noqa: E402,F401 -- re-exported for test files

AREA_NAME = 'STREAM-g FUB'
LOG_BASENAME = 'pytest_stream_fub_g.log'
MARKERS = (
    'coverage: Tests that collect coverage data',
    'protocol_coverage: Tests that collect protocol coverage',
    'fub: FUB (Functional Unit Block) level tests',
    'stream_g: stream-g (gatling-sequenced schedulers)',
)


def pytest_configure(config):
    configure(config, __file__, LOG_BASENAME, markers=MARKERS)


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    sessionfinish(__file__, AREA_NAME)


def pytest_ignore_collect(collection_path, config):
    return ignore_collect(collection_path)


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


def pytest_collection_modifyitems(config, items):
    """Tag every test in this area."""
    for item in items:
        item.add_marker(pytest.mark.fub)
