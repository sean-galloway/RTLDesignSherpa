# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Pytest config shared by every build in the Genesys 2 bridge-stress area.

Component level, so it is an ancestor of dv/tests and every build-*/dv/tests:
the component `dv` and `bin/` paths, log capture, the generated-directory
collection guards, the TEST_LEVEL fixture.
"""

import logging
import os
import sys

import pytest

_AREA = os.path.dirname(os.path.abspath(__file__))


def pytest_configure(config):
    # `from tbclasses.bs_harness_tb import ...`; the area path has a hyphen, so
    # it cannot be a package import.
    for sub in ('dv', 'bin'):
        path = os.path.join(_AREA, sub)
        if path not in sys.path:
            sys.path.insert(0, path)

    if not getattr(config.option, 'log_file', None):
        log_dir = os.path.join(_AREA, 'logs')
        os.makedirs(log_dir, exist_ok=True)
        config.option.log_file = os.path.join(log_dir, 'pytest_bridge_stress.log')
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
    logging.info('bridge-stress (Genesys 2) test session finished, exit=%s', exitstatus)


@pytest.fixture(scope='function')
def test_level():
    return os.environ.get('TEST_LEVEL', 'gate')
