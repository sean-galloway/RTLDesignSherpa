# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Unit tests for TBClasses/shared/filelist_utils.filelist_for() -- the
# module-keyed filelist resolution tooling TASK-005 (was TOOL-011) asked for.
# No simulator; runs against the real registry and tree.
#
#   source env_python && python3 -m pytest bin/tests -q

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / 'bin'))

from TBClasses.shared.filelist_utils import filelist_for, get_sources_from_filelist  # noqa: E402


@pytest.mark.parametrize('module,expected', [
    ('counter_bin', 'rtl/common/filelists/counter_bin.f'),
    ('fifo_async', 'rtl/cdc/filelists/fifo_async.f'),          # the CDC reorg moved this one
    ('axi_monitor_lite', 'rtl/amba/filelists/axi_monitor_lite.f'),
])
def test_named_filelist_resolves_through_the_registry(module, expected):
    assert filelist_for(REPO_ROOT, module) == expected


def test_unknown_module_raises_rather_than_guessing():
    with pytest.raises(FileNotFoundError):
        filelist_for(REPO_ROOT, 'no_such_module_anywhere')


def test_module_mode_returns_the_same_sources_as_the_path():
    by_path = get_sources_from_filelist(str(REPO_ROOT), 'rtl/common/filelists/counter_bin.f')
    by_module = get_sources_from_filelist(str(REPO_ROOT), module='counter_bin')
    assert by_path == by_module
    assert by_module[0], 'counter_bin resolved to no sources'


def test_exactly_one_of_path_or_module():
    with pytest.raises(ValueError):
        get_sources_from_filelist(str(REPO_ROOT))
    with pytest.raises(ValueError):
        get_sources_from_filelist(str(REPO_ROOT), 'rtl/common/filelists/counter_bin.f', module='counter_bin')
