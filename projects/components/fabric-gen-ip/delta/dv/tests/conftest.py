"""delta test configuration for pytest.

The coverage/log boilerplate lives in ``bin/cov_utils/conftest_base.py`` -- the
same shared base every area uses. This file declares only the area-specific
bits. No REG_LEVEL -> TEST_LEVEL stamp: every wrapper parametrizes
``test_level`` over reg_level_grid() and exports it with level_env()
(tooling BUG-004: a stamp here would override every per-cell value).
"""

import os
import sys

_here = os.path.dirname(os.path.abspath(__file__))
_repo_root = os.path.abspath(os.path.join(_here, '../../../../../..'))
for _p in (_repo_root, os.path.join(_repo_root, 'bin')):
    if _p in sys.path:
        sys.path.remove(_p)
    sys.path.insert(0, _p)

import pytest
from cov_utils.conftest_base import (
    configure,
    ignore_collect,
    sessionfinish,
)

AREA_NAME = 'delta'
LOG_BASENAME = 'pytest_delta.log'
MARKERS = (
    'delta: delta AXIS crossbar tests',
)


def pytest_configure(config):
    configure(config, __file__, LOG_BASENAME, markers=MARKERS)


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    sessionfinish(__file__, AREA_NAME)


def pytest_ignore_collect(collection_path, config):
    return ignore_collect(collection_path)
