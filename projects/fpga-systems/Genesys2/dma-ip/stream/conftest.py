# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Pytest config shared by EVERY build in this area.

Component level, because it is an ancestor of both `build-mon/dv/tests` and
`build-perf/dv/tests` -- pytest loads conftest.py from every directory between
the rootdir and a collected test, so one file here serves both builds. The two
builds previously carried near-identical copies that had already drifted (one
configured log capture and an ignore_collect rule, the other did not).

What belongs HERE: anything true of every build in the area -- the component
`dv/tbclasses` path (StreamHarnessTB, shared by both), log capture, the
generated-directory collection guards, the TEST_LEVEL fixture.

What belongs in a BUILD's conftest: only that build's own `dv/` path, for
tbclasses only it has (build-mon/dv/tbclasses/dma_slave_monitors_tb.py).
"""

import logging
import os
import sys

import pytest

_AREA = os.path.dirname(os.path.abspath(__file__))


def pytest_configure(config):
    # Component-level tbclasses: `from tbclasses.stream_harness_tb import ...`
    dv_path = os.path.join(_AREA, 'dv')
    if dv_path not in sys.path:
        sys.path.insert(0, dv_path)

    # bin/ holds the shared host libraries the TBs and tests import
    # (descriptor_builder, harness_addrs, stream_addrs, characterization).
    # stream_env would do this, but a test may import a library before it.
    bin_path = os.path.join(_AREA, 'bin')
    if bin_path not in sys.path:
        sys.path.insert(0, bin_path)

    if not getattr(config.option, 'log_file', None):
        log_dir = os.path.join(_AREA, 'logs')
        os.makedirs(log_dir, exist_ok=True)
        config.option.log_file = os.path.join(log_dir, 'pytest_stream.log')
        config.option.log_file_level = 'DEBUG'
        config.option.log_cli = True
        config.option.log_cli_level = 'INFO'


def pytest_ignore_collect(collection_path, config):
    """Never collect out of generated directories.

    `local_sim_build` holds Verilator output including COPIES of test sources;
    collecting there runs a stale duplicate of the test under a name that looks
    legitimate in the report.
    """
    path_str = str(collection_path)
    return any(part in path_str for part in ('logs', 'local_sim_build', 'sim_build',
                                             '__pycache__', 'fpga/build'))


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    logging.info('stream (Genesys 2) test session finished, exit=%s', exitstatus)


@pytest.fixture(scope='function')
def test_level():
    return os.environ.get('TEST_LEVEL', 'gate')
