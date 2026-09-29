# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""The Tcl filelist expander (make/tcl/filelist_utils.tcl, sourced by every
Vivado/Quartus flow) and the Python one (bin/FileFolderFunctions/
file_list_processor.py, used by every cocotb test) must read the same .f the
same way. Until tooling TASK-019 (2026-09-29) the Tcl side existed as eight
copies, seven of which did not know `//` is a comment, so a `// heading` line
came back as a source path. This builds one filelist that uses everything the
format allows -- `#` and `//` comments, trailing comments, +incdir+, nested -f,
a $REPO_ROOT-anchored path, a bare relative path -- and checks both expanders
produce the same sources and include dirs. (A nested -f is $REPO_ROOT-anchored,
as every repo filelist writes it: the Python side opens it verbatim, so a bare
relative -f would resolve against the caller's cwd there.)
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
TCL = ROOT / "make" / "tcl" / "filelist_utils.tcl"
sys.path.insert(0, str(ROOT / "bin" / "FileFolderFunctions"))
sys.path.insert(0, str(ROOT / "bin"))
import file_list_processor  # noqa: E402,F401  (so get_sources_from_filelist finds it whatever repo_root is)
from TBClasses.shared.filelist_utils import get_sources_from_filelist  # noqa: E402

TOP_F = """\
// Filelist: top  (a // heading, the char_top.f style)
# a hash comment
+incdir+common
// Dependencies
common/a.sv
common/b.sv   // trailing double-slash comment
fub/c.sv      # trailing hash comment
-f $REPO_ROOT/rtl/filelists/sub.f
$REPO_ROOT/rtl/shared/d.sv

top/top.sv
"""
SUB_F = """\
// nested list
+incdir+$REPO_ROOT/rtl/shared/inc
common/e.sv
"""


def _tree(root: Path) -> Path:
    rtl = root / "rtl"
    for rel in ("common/a.sv", "common/b.sv", "fub/c.sv", "shared/d.sv", "common/e.sv", "top/top.sv"):
        (rtl / rel).parent.mkdir(parents=True, exist_ok=True)
        (rtl / rel).write_text(f"module {Path(rel).stem}; endmodule\n")
    (rtl / "shared" / "inc").mkdir(parents=True)
    (rtl / "filelists").mkdir()
    (rtl / "filelists" / "top.f").write_text(TOP_F)
    (rtl / "filelists" / "sub.f").write_text(SUB_F)
    return rtl / "filelists" / "top.f"


def _tclsh():
    exe = shutil.which("tclsh")
    if not exe:
        pytest.skip("tclsh not installed")
    return exe


def _tcl_expand(filelist: Path, repo_root: Path):
    driver = filelist.parent / "drive.tcl"
    driver.write_text(f"""\
set ::env(REPO_ROOT) {{{repo_root}}}
source {{{TCL}}}
lassign [filelist::flatten {{{filelist}}}] s i d
puts [join $s "\\n"]
puts "---"
puts [join $i "\\n"]
""")
    env = dict(os.environ, REPO_ROOT=str(repo_root))
    env.setdefault("TCL_LIBRARY", "/usr/share/tcltk/tcl8.6")
    r = subprocess.run([_tclsh(), str(driver)], capture_output=True, text=True, env=env)
    assert r.returncode == 0, r.stderr
    srcs, _, incs = r.stdout.partition("\n---\n")
    return ({os.path.realpath(x) for x in srcs.split()}, {os.path.realpath(x) for x in incs.split()})


def _py_expand(filelist: Path, repo_root: Path):
    # the cocotb-side entry point: resolves bare relative paths against
    # dirname(dirname(filelist)), exactly as the Tcl side does
    srcs, incs = get_sources_from_filelist(str(repo_root), str(filelist.relative_to(repo_root)))
    return ({os.path.realpath(x) for x in srcs}, {os.path.realpath(x) for x in incs})


def test_tcl_and_python_expanders_agree(tmp_path):
    top = _tree(tmp_path)
    t_src, t_inc = _tcl_expand(top, tmp_path)
    p_src, p_inc = _py_expand(top, tmp_path)
    rtl = tmp_path / "rtl"
    expect_src = {os.path.realpath(rtl / r) for r in
                  ("common/a.sv", "common/b.sv", "fub/c.sv", "common/e.sv", "shared/d.sv", "top/top.sv")}
    assert t_src == expect_src, t_src ^ expect_src
    assert p_src == expect_src, p_src ^ expect_src
    expect_inc = {os.path.realpath(rtl / "common"), os.path.realpath(rtl / "shared" / "inc")}
    assert t_inc == expect_inc and p_inc == expect_inc


def test_tcl_expander_drops_comment_lines_not_sources(tmp_path):
    """The exact failure: a `// heading` must not surface as a '/ heading' source."""
    top = _tree(tmp_path)
    t_src, _ = _tcl_expand(top, tmp_path)
    assert not any("heading" in s or "Dependencies" in s for s in t_src)
    for s in t_src:
        assert Path(s).exists(), s
