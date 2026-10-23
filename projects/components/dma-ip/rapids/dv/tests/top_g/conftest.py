"""RAPIDS-g Top test configuration for pytest (rapids-g, rapids TASK-034).

top/conftest.py with this area's names; the markers are the product's,
since the -g runners re-host the product wrappers.
"""

import os
import sys

# Repo root + bin for the shared conftest base; the RAPIDS dv dir for the area's
# own imports (rapids_coverage, tbclasses). env_python already exports these on
# PYTHONPATH -- added here too so a bare pytest invocation still resolves them.
# NOTE the tests import fully-qualified
# (projects.components.dma_ip.rapids.dv.tbclasses.*), which resolves from the REPO
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

AREA_NAME = 'RAPIDS-g Top'
LOG_BASENAME = 'pytest_rapids_top_g.log'
MARKERS = (
    'coverage: Tests that collect coverage data',
    'protocol_coverage: Tests that collect protocol coverage',
    'top: Top-level tests of the byte-granular RAPIDS (rapids TASK-019)',
    'rapids_top: rapids_top tests',
    'rapids_cxs_top: rapids_cxs_top tests (CXS network planes)',
    'rapids_core: rapids_core tests',
    'rapids_g: rapids-g (gatling-sequenced schedulers)',
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
    from projects.components.dma_ip.rapids.dv.rapids_coverage.coverage_config import (
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
