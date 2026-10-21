# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Teeth for bin/check_formal_flat_sources.py: a hand-listed formal flat fails."""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECK = ROOT / "bin" / "check_formal_flat_sources.py"


def _run(root: Path) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(CHECK), "--root", str(root)],
                          capture_output=True, text=True)


def _unit(root: Path, name: str, makefile: str) -> None:
    d = root / "formal" / "demo" / name
    d.mkdir(parents=True)
    (d / "Makefile").write_text(makefile)


def test_hand_listed_flat_fails(tmp_path: Path) -> None:
    _unit(tmp_path, "bad", "SRCS := a.sv b.sv\nbad_flat.v: $(SRCS)\n\tsv2v $(SRCS) > $@\n")
    r = _run(tmp_path)
    assert r.returncode == 1, r.stdout
    assert "HANDLISTED formal/demo/bad/Makefile" in r.stdout


def test_include_passes_and_comments_do_not_count(tmp_path: Path) -> None:
    _unit(tmp_path, "good", "FLAT := good_flat.v\nFLAT_FILELIST := x.f\n"
                            "include $(REPO_ROOT)/make/formal_flat.mk\n")
    _unit(tmp_path, "notes", "# was: notes_flat.v built by hand\nprove:\n\tsby -f x.sby\n")
    r = _run(tmp_path)
    assert r.returncode == 0, r.stdout


def test_commented_include_does_not_satisfy(tmp_path: Path) -> None:
    _unit(tmp_path, "sneaky", "# include $(REPO_ROOT)/make/formal_flat.mk\n"
                              "sneaky_flat.v: a.sv\n\tsv2v a.sv > $@\n")
    assert _run(tmp_path).returncode == 1


def test_repo_is_clean() -> None:
    r = _run(ROOT)
    assert r.returncode == 0, r.stdout


_INC = "FLAT_FILELIST := x.f\ninclude $(REPO_ROOT)/make/formal_flat.mk\n"


def test_flat_in_a_subdirectory_fails(tmp_path: Path) -> None:
    # kestrel 2026-10-20: genchecks.py rmtree'd checks/, taking checks/rtl_v/'s
    # flat with it before sby ran; the include rule alone passed that Makefile.
    _unit(tmp_path, "sub", "CHECKS_DIR := $(CURDIR)/checks\nRTL_V := $(CHECKS_DIR)/rtl_v\n"
                           "FLAT := $(RTL_V)/sub_flat.v\n" + _INC)
    r = _run(tmp_path)
    assert r.returncode == 1, r.stdout
    assert "FLAT_SUBDIR formal/demo/sub/Makefile: FLAT := $(RTL_V)/sub_flat.v" in r.stdout


def test_flat_in_the_unit_directory_passes(tmp_path: Path) -> None:
    _unit(tmp_path, "bare", "FLAT := bare_flat.v\n" + _INC)
    _unit(tmp_path, "curdir", "FLAT := $(CURDIR)/curdir_flat.v\n" + _INC)
    r = _run(tmp_path)
    assert r.returncode == 0, r.stdout


def test_old_kestrel_makefile_fails(tmp_path: Path) -> None:
    old = subprocess.run(["git", "-C", str(ROOT), "show",
                          "db6fc7f2e:formal/kestrel/riscv-formal/Makefile"],
                         capture_output=True, text=True, check=True).stdout
    _unit(tmp_path, "kestrel", old)
    r = _run(tmp_path)
    assert r.returncode == 1, r.stdout
    assert "FLAT_SUBDIR" in r.stdout
