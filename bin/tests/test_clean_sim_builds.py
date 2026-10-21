# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_clean_sim_builds
# Purpose: Teeth for `bin/clean_sim_builds.py` -- a live build must survive a
#          clean, including one that starts after the cleaner listed the
#          container.
#
# Created: 2026-10-21

"""Liveness tests for the sim-build cleaner.

The race test patches ``os.listdir`` inside the module so a run calls
``sim_build_path()`` between the cleaner's snapshot of the container and its
removal of it. Before the fix the container went with ``rmtree`` once nothing
in the snapshot was busy, taking the late build, marker and all, with it.
"""

import os
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "bin"))

import clean_sim_builds as csb  # noqa: E402


def _mark(path, pid):
    path.mkdir(parents=True)
    (path / ".sim_busy").write_text(
        f"session=test\npid={pid}\nstarted={time.time():.0f}\n")


def test_stale_build_removed_and_container_dropped(tmp_path):
    cont = tmp_path / "local_sim_build"
    _mark(cont / "dead_build", 2 ** 22 + 1)      # no such pid
    (cont / "stray.log").write_text("x")
    removed, skipped = csb.clean_container(str(cont))
    assert len(removed) == 1 and not skipped
    assert not cont.exists()


def test_live_build_skipped(tmp_path):
    cont = tmp_path / "local_sim_build"
    _mark(cont / "live_build", os.getppid())
    removed, skipped = csb.clean_container(str(cont))
    assert not removed and len(skipped) == 1
    assert (cont / "live_build").is_dir()


def test_build_started_after_listdir_survives(tmp_path, monkeypatch):
    cont = tmp_path / "local_sim_build"
    _mark(cont / "dead_build", 2 ** 22 + 1)
    late = cont / "late_live_build"
    real_listdir = os.listdir

    def racing_listdir(p):
        out = real_listdir(p)
        if Path(p) == cont:
            _mark(late, os.getppid())            # a run starts right now
        return out

    monkeypatch.setattr(csb.os, "listdir", racing_listdir)
    removed, skipped = csb.clean_container(str(cont))
    assert len(removed) == 1 and not skipped
    assert (late / ".sim_busy").is_file()
