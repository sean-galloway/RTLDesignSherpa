"""Bridge Validation Test Configuration for pytest.

Configures the test environment for AXI4 Bridge crossbar validation.
The boilerplate (log dir setup, coverage aggregation, scratch-dir
ignore) lives in ``bin/cov_utils/conftest_base.py``; this file just
declares the bridge-specific bits.

Coverage Features:
- Set COVERAGE=1 to enable code coverage collection
- Set COVERAGE_PROTOCOL=1 to enable protocol coverage collection
- Coverage reports are aggregated at session end
"""

import os
import sys

# Add repository paths before any test imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, repo_root)
sys.path.insert(0, os.path.join(repo_root, 'bin'))

import pytest
from cov_utils.conftest_base import configure, sessionfinish, ignore_collect
from cov_utils.conftest_coverage import get_coverage_compile_args  # noqa: F401 — re-exported for test files

AREA_NAME = 'Bridge'
LOG_BASENAME = 'pytest_bridge.log'

MARKERS = (
    'bridge: Bridge crossbar tests',
    'basic: Basic functionality tests',
    'routing: Address decode and routing tests',
    'arbitration: Round-robin arbitration tests',
    'concurrent: Concurrent path tests',
    'stress: Stress testing',
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


def pytest_collection_modifyitems(config, items):
    """Auto-tag tests with bridge-specific markers based on node-id substrings."""
    for item in items:
        nid = item.nodeid
        if 'routing' in nid:
            item.add_marker(pytest.mark.routing)
        elif 'arbitration' in nid:
            item.add_marker(pytest.mark.arbitration)
        elif 'concurrent' in nid:
            item.add_marker(pytest.mark.concurrent)
        elif 'stress' in nid:
            item.add_marker(pytest.mark.stress)
        elif 'basic' in nid:
            item.add_marker(pytest.mark.basic)


# ----------------------------------------------------------------------
# Bridge-specific parametrization fixtures (kept local to this area).
# ----------------------------------------------------------------------

@pytest.fixture(scope='module', params=[
    # (num_masters, num_slaves, data_width, addr_width, id_width)
    (2, 2, 32, 32, 4),   # Basic 2x2 crossbar
    (2, 4, 32, 32, 4),   # 2 masters, 4 slaves
    (4, 2, 32, 32, 4),   # 4 masters, 2 slaves
    (4, 4, 32, 32, 4),   # Full 4x4 crossbar
])
def bridge_config(request):
    """Bridge crossbar configuration parameters."""
    num_masters, num_slaves, data_width, addr_width, id_width = request.param
    return {
        'NUM_MASTERS': num_masters,
        'NUM_SLAVES': num_slaves,
        'DATA_WIDTH': data_width,
        'ADDR_WIDTH': addr_width,
        'ID_WIDTH': id_width,
    }


@pytest.fixture(scope='module', params=[
    # (level, transaction_count, timeout_factor)
    ('gate', 10, 1.0),
    ('func', 50, 1.5),
    ('full', 200, 2.0),
])
def bridge_test_level(request):
    """Bridge test level configuration; ``TEST_LEVEL`` env var overrides."""
    level, transaction_count, timeout_factor = request.param
    env_level = os.environ.get('TEST_LEVEL', level).lower()
    if env_level in ['gate', 'func', 'full']:
        level = env_level
    return {
        'level': level,
        'transaction_count': transaction_count,
        'timeout_factor': timeout_factor,
    }


def get_bridge_env_config():
    """Bridge configuration from environment variables."""
    return {
        'NUM_MASTERS': int(os.environ.get('BRIDGE_NUM_MASTERS', '2')),
        'NUM_SLAVES': int(os.environ.get('BRIDGE_NUM_SLAVES', '2')),
        'DATA_WIDTH': int(os.environ.get('BRIDGE_DATA_WIDTH', '32')),
        'ADDR_WIDTH': int(os.environ.get('BRIDGE_ADDR_WIDTH', '32')),
        'ID_WIDTH': int(os.environ.get('BRIDGE_ID_WIDTH', '4')),
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', 'gate').lower(),
        'ENABLE_WAVEDUMP': os.environ.get('ENABLE_WAVEDUMP', '1') == '1',
    }


@pytest.fixture(scope='function')
def coverage_enabled():
    """Whether coverage collection is enabled for this run."""
    return os.environ.get('COVERAGE', '0') == '1'


@pytest.fixture(scope='function')
def test_level():
    """Test level (overridable via ``TEST_LEVEL`` env var)."""
    return os.environ.get('TEST_LEVEL', 'gate')
