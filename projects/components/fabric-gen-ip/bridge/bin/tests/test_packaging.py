# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Unit tests for the installable generator (GitHub #119 L6): the bundled RTL
# closure, the package's own flattener, and where generated paths anchor.
#
# The out-of-repo proof (build the wheel, install it in a clean venv, generate,
# flatten, lint) is `make package-check`; these are the fast checks that keep
# its inputs honest.
#
# Run:  pytest projects/components/fabric-gen-ip/bridge/bin/tests -q   (or `make test`)

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

BIN_DIR = Path(__file__).resolve().parents[1]
REPO_ROOT = BIN_DIR.parents[4]
BRIDGE_DIR = BIN_DIR.parent
sys.path.insert(0, str(BIN_DIR))

from bridge_pkg import _paths, ip_closure                  # noqa: E402
from bridge_pkg.flatten import flatten                      # noqa: E402


def _fixture(name: str) -> str:
    return str(BIN_DIR / "test_configs" / name)


def test_paths_find_this_checkout():
    assert _paths.rds_root() == REPO_ROOT
    assert _paths.ip_root() == REPO_ROOT
    assert _paths.regmap_tool() == REPO_ROOT / "bin" / "peakrdl_generate.py"


def test_closure_resolves_with_the_known_anchors():
    c = ip_closure.closure(REPO_ROOT)
    for must in ("projects/components/fabric-gen-ip/bridge/rtl/bridge_cam.sv",
                 "rtl/amba/axi4/axi4_subtractive_slave.sv",
                 "formal/bridge/axi4_protocol_checker.sv",
                 "rtl/amba/filelists/reset_defs.f"):
        assert must in c.files, f"{must} missing from the bundled closure"
    assert all((REPO_ROOT / f).is_file() for f in c.files)
    assert "rtl/amba/includes" in c.incdirs


def test_closure_covers_every_committed_bridge():
    """The wheel bundles the closure; every source any committed bridge
    compiles (other than its own generated files) must be in it, or an
    installed user generating that config gets a missing file."""
    c = ip_closure.closure(REPO_ROOT)
    headers = {str(p.relative_to(REPO_ROOT)) for d in c.incdirs
               for p in (REPO_ROOT / d).glob("*.svh")}
    lists = sorted((BRIDGE_DIR / "rtl" / "filelists").glob("*.f"))
    assert len(lists) > 50, "expected the full committed bridge set"
    missing = set()
    for fl in lists:
        for entry in flatten(fl):
            if entry.startswith("+incdir+"):
                continue
            rel = str(Path(entry).relative_to(REPO_ROOT))
            if "/rtl/generated/" in rel or rel.endswith("_checkers.sv"):
                continue
            if rel not in c.sources and rel not in headers:
                missing.add(f"{fl.name}: {rel}")
    assert not missing, "not in the bundled closure:\n  " + "\n  ".join(sorted(missing))


def test_unknown_template_field_fails_loudly(tmp_path, monkeypatch):
    src = tmp_path / "gen.py"
    src.write_text('x = "-f $REPO_ROOT/rtl/amba/filelists/{bogus}.f"\n')
    monkeypatch.setattr(ip_closure, "GENERATOR_SOURCES", (src,))
    with pytest.raises(ValueError, match="bogus"):
        ip_closure.seeds(REPO_ROOT)


def test_flatten_dedups_in_first_seen_order(tmp_path):
    a, b, c = (tmp_path / n for n in ("a.sv", "b.sv", "c.sv"))
    for f in (a, b, c):
        f.write_text("")
    (tmp_path / "inc").mkdir()
    (tmp_path / "x.f").write_text("+incdir+inc\na.sv\nb.sv\n")
    (tmp_path / "y.f").write_text("b.sv\nc.sv\n")
    (tmp_path / "top.f").write_text("// comment\n-f x.f\n-f y.f\n-f x.f\na.sv\n")
    out = flatten(tmp_path / "top.f")
    assert out == [f"+incdir+{tmp_path / 'inc'}", str(a), str(b), str(c)]


@pytest.mark.parametrize("bridge", ["bridge_2x2_rw", "bridge_mix_e"])
def test_flatten_matches_the_repo_flattener(bridge):
    fl = BRIDGE_DIR / "rtl" / "filelists" / f"{bridge}.f"
    mine = [e for e in flatten(fl) if not e.startswith("+incdir+")]
    r = subprocess.run(
        [sys.executable, str(REPO_ROOT / "bin" / "flatten_filelist.py"), str(fl),
         "--resolve-env", "--absolute-paths"],
        env=dict(os.environ, REPO_ROOT=str(REPO_ROOT)),
        capture_output=True, text=True, timeout=120)
    assert r.returncode == 0, r.stderr
    ref = [ln.strip() for ln in r.stdout.splitlines()
           if ln.strip() and not ln.startswith(("#", "+incdir"))]
    assert sorted(mine) == sorted(set(ref))
    assert len(mine) == len(set(mine))


def test_foreign_git_repo_does_not_claim_repo_root(tmp_path):
    """Generated into somebody else's repository, the bridge's own files are
    filelist-relative: $REPO_ROOT there means the IP root, not that repo."""
    (tmp_path / ".git").mkdir()
    out = tmp_path / "rtl" / "generated"
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", _fixture("bridge_1x2_rd_matched.toml"),
         "--connectivity", _fixture("bridge_1x2_rd_matched_connectivity.csv"),
         "--name", "bridge_1x2_rd", "--output-dir", str(out)],
        cwd=str(BIN_DIR), env=dict(os.environ, REPO_ROOT=str(REPO_ROOT)),
        capture_output=True, text=True, timeout=300)
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"
    fl = tmp_path / "rtl" / "filelists" / "bridge_1x2_rd.f"
    own = [ln for ln in fl.read_text().splitlines() if "bridge_1x2_rd/" in ln]
    assert own and all(ln.startswith("../generated/bridge_1x2_rd/") for ln in own), own
    flat = flatten(fl)
    assert any(e.endswith("/bridge_1x2_rd/bridge_1x2_rd.sv") for e in flat)
