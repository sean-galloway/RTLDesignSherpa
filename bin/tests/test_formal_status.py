# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_formal_status
# Purpose: Teeth for `bin/formal_status.py --check-flats` (tooling TASK-026) --
#          a planted-staleness mutation test proving the mode catches a
#          committed sv2v flat that has drifted from its sources.
#
# Created: 2026-10-03

"""Planted-staleness tests for formal flat self-detection.

House rule (TASK-026 "Done when"): a mutation test proves the mode fails when
a flat is behind its source. The fixture builds a scratch repo holding one
flatten-flow proof (``formal/demo/block1``) with a real committed sv2v flat,
then lets a test drift the source without regenerating -- the exact failure
the mode exists to catch.

The script under test is COPIED into the scratch repo, not imported: ROOT is
derived from the script's own location, and ``--areas demo`` must resolve
against the scratch tree, not this repository.
"""

import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
STATUS = ROOT / "bin" / "formal_status.py"

# sv2v is not on PATH everywhere; /mnt/data/tools is where this machine keeps
# v0.0.13. The mode's own discovery has the same fallback, so tests use it too.
SV2V_DIR = "/mnt/data/tools"


def _env_with_sv2v() -> dict:
    env = dict(os.environ)
    env["PATH"] = SV2V_DIR + os.pathsep + env.get("PATH", "")
    return env


def make_flat_repo(tmp_path: Path, recipe_body: str,
                   drift: bool = False,
                   dut_body: str | None = None) -> Path:
    """A scratch repo with one flatten-flow proof and a committed flat.

    ``recipe_body`` replaces the flat rule's recipe lines so the UNHANDLED
    case can plant an in-tree side effect. ``drift`` mutates the source after
    the flat is generated, planting staleness without touching the flat.
    ``dut_body`` replaces the default trivial DUT (tests that need sv2v to
    bake source locations into the flat pass an asserting design).
    """
    repo = tmp_path / "scratch"
    proof = repo / "formal" / "demo" / "block1"
    proof.mkdir(parents=True)
    (repo / "bin").mkdir()

    shutil.copy(STATUS, repo / "bin" / "formal_status.py")

    if dut_body is None:
        dut_body = (
            "module dut(input  logic        clk,\n"
            "           input  logic [7:0] d,\n"
            "           output logic [7:0] q);\n"
            "  assign q = d;\n"
            "endmodule\n")
    (proof / "dut.sv").write_text(dut_body)
    (proof / "block1.sby").write_text(
        "[options]\nmode bmc\n[script]\n"
        "read_verilog -formal block1_flat.v\n")
    (proof / "Makefile").write_text(
        "SV2V ?= sv2v\n"
        "block1_flat.v: dut.sv\n"
        + recipe_body)

    # Generate the committed flat with the proof's own Makefile, exactly as
    # a developer would. The recipe may side-effect in-tree (the UNHANDLED
    # case plants one); that artifact belongs to the GENERATION, not to the
    # check under test, so remove it and let the assertion below prove the
    # checker never re-creates it.
    subprocess.run(["make", "block1_flat.v"], cwd=proof, check=True,
                   env=_env_with_sv2v(),
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    (proof / "side_effect.txt").unlink(missing_ok=True)

    if drift:
        (proof / "dut.sv").write_text(
            "module dut(input  logic         clk,\n"
            "           input  logic [15:0] d,\n"
            "           output logic [15:0] q);\n"
            "  assign q = d;\n"
            "endmodule\n")

    return repo


def run_check(repo: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, "bin/formal_status.py", "--check-flats", "--areas", "demo"],
        cwd=repo, env=_env_with_sv2v(),
        capture_output=True, text=True)


SIMPLE_RECIPE = "\t$(SV2V) dut.sv > $@\n"

# The REPO_ROOT pattern real formal Makefiles use: absolute source paths, so
# sv2v bakes the generating clone's checkout path into the flat.
ABS_RECIPE = "\t$(SV2V) $(CURDIR)/dut.sv > $@\n"

UNHANDLED_RECIPE = (
    "\t$(SV2V) dut.sv > $@\n"
    "\ttouch side_effect.txt\n")


def test_stale_flat_fails(tmp_path):
    """A source mutated after the flat was committed reports STALE."""
    repo = make_flat_repo(tmp_path, SIMPLE_RECIPE, drift=True)
    r = run_check(repo)
    assert r.returncode == 1, \
        f"expected exit 1, got {r.returncode}: {r.stdout}{r.stderr}"
    assert "STALE" in r.stdout
    assert "demo/block1" in r.stdout


def test_current_flat_passes(tmp_path):
    """A flat regenerated from the same source reports CURRENT, exit 0."""
    repo = make_flat_repo(tmp_path, SIMPLE_RECIPE)
    r = run_check(repo)
    assert r.returncode == 0, \
        f"expected exit 0, got {r.returncode}: {r.stdout}{r.stderr}"
    assert "CURRENT" in r.stdout


def test_reformatted_flat_is_current(tmp_path):
    """A post-formatter flat -- one token per line, whitespace only --
    still reports CURRENT. Committed flats may be formatted after sv2v
    ([[reference_committed_sv_is_post_formatter]]); the comparison is
    token-based, so formatting alone must never flag STALE."""
    repo = make_flat_repo(tmp_path, SIMPLE_RECIPE)
    flat = repo / "formal" / "demo" / "block1" / "block1_flat.v"
    flat.write_text("\n".join(flat.read_text().split()) + "\n")
    r = run_check(repo)
    assert r.returncode == 0, \
        f"a whitespace-only reformat flagged drift: {r.stdout}{r.stderr}"
    assert "CURRENT" in r.stdout


def test_foreign_checkout_root_is_current(tmp_path):
    """A flat committed from a DIFFERENT clone's absolute root must not flag
    STALE on this runner. Formal Makefiles export REPO_ROOT (git rev-parse
    --show-toplevel) and pass absolute source paths, so sv2v bakes the
    generating machine's checkout path into assertion source locations
    (dev machine: /mnt/data/github/RTLDesignSherpa, CI: /home/runner/work/...)
    -- same design, different prefix. The comparison masks any absolute
    prefix entering the repo tree; a path-only difference is not drift."""
    repo = make_flat_repo(
        tmp_path, ABS_RECIPE,
        dut_body=(
            "module dut #(parameter int W = 1) (\n"
            "           input  logic        clk,\n"
            "           input  logic [7:0] d,\n"
            "           output logic [7:0] q);\n"
            "  assign q = d;\n"
            "  generate\n"
            "    if (W < 2) begin : gen_guard\n"
            "      $error(\"unsupported W=%0d\", W);\n"
            "    end\n"
            "  endgenerate\n"
            "endmodule\n"))
    flat = repo / "formal" / "demo" / "block1" / "block1_flat.v"
    assert str(repo) in flat.read_text(), \
        "fixture must bake an absolute checkout path into the flat"
    flat.write_text(flat.read_text().replace(
        str(repo), "/home/runner/work/RTLDesignSherpa/RTLDesignSherpa"))
    r = run_check(repo)
    assert r.returncode == 0, \
        f"a foreign checkout root flagged drift: {r.stdout}{r.stderr}"
    assert "CURRENT" in r.stdout


def test_unhandled_recipe_reported(tmp_path):
    """A recipe that writes in-tree is UNHANDLED and never executes."""
    repo = make_flat_repo(tmp_path, UNHANDLED_RECIPE)
    r = run_check(repo)
    assert r.returncode == 1
    assert "UNHANDLED" in r.stdout
    assert not (repo / "formal" / "demo" / "block1" / "side_effect.txt").exists(), \
        "the in-tree side effect ran -- the tree was not protected"


def _git(repo: Path, *args: str):
    return subprocess.run(["git", "-C", str(repo), *args],
                          capture_output=True, text=True, check=True)


def _git_repo(tmp_path, drift: bool) -> Path:
    repo = make_flat_repo(tmp_path, SIMPLE_RECIPE, drift=drift)
    _git(repo, "init", "-q")
    _git(repo, "add", "-A")
    _git(repo, "-c", "user.email=t@example.com", "-c", "user.name=t",
         "commit", "-qm", "init")
    return repo


def _run_staged(repo: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, "bin/formal_status.py", "--check-flats", "--staged",
         "--areas", "demo"],
        cwd=repo, env=_env_with_sv2v(),
        capture_output=True, text=True)


def _drift_source(repo: Path):
    """Widen the port after the flat was committed: planted staleness."""
    dut = repo / "formal" / "demo" / "block1" / "dut.sv"
    dut.write_text(dut.read_text().replace("[7:0]", "[15:0]"))


def test_staged_mode_catches_drifted_source(tmp_path):
    """The pre-commit shape: source staged, flat untouched -> still caught."""
    repo = _git_repo(tmp_path, drift=False)
    _drift_source(repo)
    _git(repo, "add", "formal/demo/block1/dut.sv")
    r = _run_staged(repo)
    assert r.returncode == 1, \
        f"expected exit 1, got {r.returncode}: {r.stdout}{r.stderr}"
    assert "STALE" in r.stdout
    assert "demo/block1" in r.stdout


def test_staged_mode_skips_untouched_proofs(tmp_path):
    """Drift on disk but nothing staged -> nothing checked."""
    repo = _git_repo(tmp_path, drift=False)
    _drift_source(repo)
    r = _run_staged(repo)
    assert r.returncode == 0, \
        f"expected exit 0, got {r.returncode}: {r.stdout}{r.stderr}"
    assert "checked=0" in r.stdout


def test_staged_mode_catches_staged_flat(tmp_path):
    """Staging the flat file itself selects the proof, even when no source
    is staged -- the 'regenerated flat restaged' half of the filter. The
    reformat is whitespace-only, so the proof still reports CURRENT."""
    repo = _git_repo(tmp_path, drift=False)
    flat = repo / "formal" / "demo" / "block1" / "block1_flat.v"
    flat.write_text("\n".join(flat.read_text().split()) + "\n")
    _git(repo, "add", "formal/demo/block1/block1_flat.v")
    r = _run_staged(repo)
    assert r.returncode == 0, \
        f"expected exit 0, got {r.returncode}: {r.stdout}{r.stderr}"
    assert "checked=1" in r.stdout
    assert "CURRENT" in r.stdout


def test_gitignored_flat_area_is_skipped(tmp_path):
    """An area that gitignores *_flat.v (the formal/pumice pattern) skips
    cleanly instead of failing -- there is no committed flat to go stale."""
    repo = tmp_path / "scratch"
    proof = repo / "formal" / "demo" / "block1"
    proof.mkdir(parents=True)
    (repo / "bin").mkdir()
    shutil.copy(STATUS, repo / "bin" / "formal_status.py")
    (proof / "Makefile").write_text(
        "SV2V ?= sv2v\n"
        "block1_flat.v: dut.sv\n"
        "\t$(SV2V) dut.sv > $@\n")
    (proof / "block1.sby").write_text("[options]\nmode bmc\n")
    (proof / "dut.sv").write_text(
        "module dut(input  logic [7:0] d, output logic [7:0] q);\n"
        "  assign q = d;\nendmodule\n")
    (proof / ".gitignore").write_text("*_flat.v\n")
    _git(repo, "init", "-q")
    r = subprocess.run(
        [sys.executable, "bin/formal_status.py", "--check-flats", "--areas", "demo"],
        cwd=repo, env=_env_with_sv2v(),
        capture_output=True, text=True)
    assert r.returncode == 0, \
        f"expected exit 0, got {r.returncode}: {r.stdout}{r.stderr}"
    assert "skipped=1" in r.stdout
