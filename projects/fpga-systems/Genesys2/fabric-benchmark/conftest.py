# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Pytest config shared by every build in the Genesys 2 fabric-benchmark area.

Component level so it is an ancestor of the area's dv/tests and every
build-*/dv/tests (same layout as Genesys2/dma-ip/stream): the component
`dv/tbclasses` and `bin/` paths, log capture, the generated-directory
collection guards, the TEST_LEVEL fixture.
"""

import logging
import os
import sys

import pytest

_AREA = os.path.dirname(os.path.abspath(__file__))


def pytest_configure(config):
    # `from tbclasses.fb_fabric_tb import ...`; the area path has hyphens, so
    # it cannot be a package import.
    for sub in ('dv', 'bin'):
        path = os.path.join(_AREA, sub)
        if path not in sys.path:
            sys.path.insert(0, path)

    if not getattr(config.option, 'log_file', None):
        log_dir = os.path.join(_AREA, 'logs')
        os.makedirs(log_dir, exist_ok=True)
        config.option.log_file = os.path.join(log_dir, 'pytest_fabric_benchmark.log')
        config.option.log_file_level = 'DEBUG'
        config.option.log_cli = True
        config.option.log_cli_level = 'INFO'


def pytest_ignore_collect(collection_path, config):
    """Never collect out of generated directories (Verilator copies test sources)."""
    path_str = str(collection_path)
    return any(part in path_str for part in ('logs', 'local_sim_build', 'sim_build',
                                             '__pycache__', 'fpga/build'))


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    logging.info('fabric-benchmark (Genesys 2) test session finished, exit=%s', exitstatus)


@pytest.fixture(scope='function')
def test_level():
    return os.environ.get('TEST_LEVEL', 'gate')
