# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Teeth for bin/flatten_filelist.py's failure paths.

Every lint and formal gate flattens its filelist through this script, so a bad
input must stop it with a message that names the file, never hand the tool a
partial design. A missing nested -f used to die with a bare
"ValueError: not enough values to unpack (expected 4, got 3)" that named
nothing; it is now a named error, exit 2, like an include cycle. Pinned here,
with the good path for contrast.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FLATTEN = ROOT / "bin" / "flatten_filelist.py"


def _run(top: Path) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(FLATTEN), str(top)],
                          capture_output=True, text=True)


def test_nested_filelists_flatten(tmp_path: Path) -> None:
    (tmp_path / "a.sv").write_text("module a; endmodule\n")
    (tmp_path / "inner.f").write_text(f"{tmp_path / 'a.sv'}\n")
    (tmp_path / "top.f").write_text(f"-f {tmp_path / 'inner.f'}\n")
    r = _run(tmp_path / "top.f")
    assert r.returncode == 0, r.stderr
    assert str(tmp_path / "a.sv") in r.stdout


def test_missing_nested_filelist_is_a_named_error(tmp_path: Path) -> None:
    (tmp_path / "inner.f").write_text(f"-f {tmp_path / 'gone.f'}\n")
    (tmp_path / "top.f").write_text(f"-f {tmp_path / 'inner.f'}\n")
    r = _run(tmp_path / "top.f")
    assert r.returncode == 2, (r.returncode, r.stderr)
    assert "ValueError" not in r.stderr and "Traceback" not in r.stderr, r.stderr
    assert "cannot find filelist" in r.stderr and "gone.f" in r.stderr, r.stderr
    # The include chain, in order, outermost first
    assert f"{tmp_path / 'top.f'} -> {tmp_path / 'inner.f'}" in r.stderr, r.stderr


def test_include_cycle_is_a_named_error(tmp_path: Path) -> None:
    (tmp_path / "a.f").write_text(f"-f {tmp_path / 'b.f'}\n")
    (tmp_path / "b.f").write_text(f"-f {tmp_path / 'a.f'}\n")
    r = _run(tmp_path / "a.f")
    assert r.returncode == 2, (r.returncode, r.stderr)
    assert f"{tmp_path / 'a.f'} -> {tmp_path / 'b.f'} -> {tmp_path / 'a.f'}" in r.stderr, r.stderr
