"""STREAM-g top-level test configuration for pytest (stream-g, stream TASK-020).

top/conftest.py with this area's names, plus the re-host: every product top
test collected here (see test_stream_g_top*.py) runs its own cocotb test and
parameters, but against the stream-g top. The product test files are not
edited; the `run` they call (cocotb_test.simulator.run, imported inside the
wrapper) is replaced for the duration of each test by one that
    stream_top_ch8  -> stream_g_top_ch8      (rtl/filelists/top_g/)
    stream_top_ch16 -> stream_g_top_ch16
with the build and the logs kept in this directory, so a clean-all here never
touches the product's.
"""

import os
import sys

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
PRODUCT_DIR = os.path.abspath(os.path.join(_here, '../top'))
if PRODUCT_DIR not in sys.path:
    sys.path.insert(0, PRODUCT_DIR)

import pytest  # noqa: E402
import cocotb_test.simulator  # noqa: E402
from cov_utils.conftest_base import configure, sessionfinish, ignore_collect  # noqa: E402
from cov_utils.conftest_coverage import get_coverage_compile_args  # noqa: E402,F401 -- re-exported for test files
from TBClasses.shared.filelist_utils import get_sources_from_filelist  # noqa: E402

AREA_NAME = 'STREAM-g Top'
LOG_BASENAME = 'pytest_stream_top_g.log'
MARKERS = (
    'coverage: Tests that collect coverage data',
    'protocol_coverage: Tests that collect protocol coverage',
    'stream_g: stream-g (gatling-sequenced schedulers)',
)

G_TOP = {'stream_top_ch8': 'stream_g_top_ch8', 'stream_top_ch16': 'stream_g_top_ch16'}
_PRODUCT_RUN = cocotb_test.simulator.run


def _rehosted(path: str) -> str:
    """A product path under tests/top, moved under tests/top_g with a -g name."""
    return path.replace('/tests/top/', '/tests/top_g/').replace('test_stream_top', 'test_stream_g_top')


def _run_on_g(*args, **kw):
    """cocotb_test.simulator.run, re-pointed at the stream-g top."""
    dut = kw.get('toplevel')
    if dut not in G_TOP:
        pytest.skip(f"stream-g has no {dut}")
    g_dut = G_TOP[dut]
    # one gatling serves 4, 8 or 16 channels (rapids_seq_g); the product's
    # 1- and 2-channel cells have no stream-g counterpart, nor do its
    # per-channel-engine builds
    params = kw.get('parameters') or {}
    nch = int(params.get('NUM_CHANNELS', 8))
    if nch not in (4, 8, 16):
        pytest.skip(f"stream-g: no {nch}-channel top (one gatling serves 4, 8 or 16 channels)")
    if int(params.get('SHARED_ENGINES', 1)) == 0:
        pytest.skip("stream-g: the schedulers exist only in the shared-engine structure (SHARED_ENGINES = 1)")
    sources, includes = get_sources_from_filelist(
        repo_root=_repo_root, filelist_path=f'projects/components/dma-ip/stream/rtl/filelists/top_g/{g_dut}.f')
    kw['toplevel'] = g_dut
    kw['verilog_sources'] = sources
    kw['includes'] = includes
    if kw.get('sim_build'):
        kw['sim_build'] = _rehosted(kw['sim_build'])
        os.makedirs(kw['sim_build'], exist_ok=True)
    env = dict(kw.get('extra_env') or {})
    for key in ('LOG_PATH', 'COCOTB_RESULTS_FILE', 'COCOTB_TRACE_FILE'):
        if key in env:
            env[key] = _rehosted(env[key])
            os.makedirs(os.path.dirname(env[key]), exist_ok=True)
    env['DUT'] = g_dut
    env['TEST_STREAM_G'] = '1'           # the TB drives seq_restart (StreamCoreTB)
    kw['extra_env'] = env
    return _PRODUCT_RUN(*args, **kw)


@pytest.fixture(autouse=True)
def _rehost_run(monkeypatch):
    """Every test in this directory runs on the stream-g top."""
    monkeypatch.setattr(cocotb_test.simulator, 'run', _run_on_g)
    yield


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


@pytest.fixture(scope="function")
def coverage_config():
    """STREAM functional-coverage config (stream_coverage package)."""
    from projects.components.dma_ip.stream.dv.stream_coverage.coverage_config import (
        StreamCoverageConfig,
    )
    return StreamCoverageConfig.from_environment()


def pytest_collection_modifyitems(config, items):
    for item in items:
        item.add_marker(pytest.mark.stream_g)
