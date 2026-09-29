# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Tests for bin/check_port_consumers.py (tooling BUG-013).

The checker's own opening line is "adding a port to a module breaks every
consumer that does not connect it", and for one common port shape -- an
UNPACKED array -- it did not notice: the port regex did not match the line,
the port never entered the set, and the consumer's PINMISSING was filtered
out as "not this change". Sixteen pumice tests failed to build behind a green
run. A checker whose blind spot is untested is how that reached its third
instance, so:

  * port_set() is pinned on every declaration shape, including the ones the
    old regex missed (a mutation to the old regex fails this test);
  * unexplained_pins() is pinned: a pin Verilator names that the parser did
    not put in the touched set, but whose name differs between the old and
    new headers, is reported rather than dropped;
  * an END-TO-END case in a scratch git repo: a module gains an unpacked-array
    port, its consumer does not connect it, and the checker must return 1 and
    name the pin. Then the consumer is fixed and it must return 0.
"""
from __future__ import annotations

import importlib.util
import os
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "bin" / "check_port_consumers.py"
_spec = importlib.util.spec_from_file_location("cpc", CHECKER)
cpc = importlib.util.module_from_spec(_spec)
sys.modules["cpc"] = cpc
_spec.loader.exec_module(cpc)

SIX_PORTS = textwrap.dedent("""\
    module t #(parameter int NUM_BANKS = 4, parameter int W = 32) (
        input  logic clk,
        output logic plain_port_o,
        output logic [W-1:0] vec_port_o,
        output logic [31:0] array_port_o [NUM_BANKS],
        output logic [7:0]  two_dim_o [2][NUM_BANKS], // a comment after the dims
        input  logic last_port_i
    );
    endmodule
    """)


def test_port_set_sees_every_shape():
    assert cpc.port_set(SIX_PORTS) == {
        "clk", "plain_port_o", "vec_port_o", "array_port_o", "two_dim_o", "last_port_i"}


def test_port_set_does_not_take_a_range_parameter_for_the_name():
    # `[W-1:0]` and `[NUM_BANKS]` carry identifiers; none of them is a port
    assert not ({"W", "NUM_BANKS"} & cpc.port_set(SIX_PORTS))


def test_unexplained_pins_reports_a_shape_the_parser_missed():
    old = "module m (input logic clk);\nendmodule"
    new = "module m (input logic clk, output logic [31:0] zz_o [4]);\nendmodule"
    lint = ["%Error-PINMISSING: tb.sv:9:5: Cell has missing pin: 'zz_o'",
            "%Error-PINMISSING: tb.sv:9:5: Cell has missing pin: 'pre_existing'"]
    # the parser (simulated) saw nothing: touched is empty
    got = cpc.unexplained_pins(lint, set(), old, new)
    assert len(got) == 1 and "'zz_o'" in got[0] and "port shape not parsed" in got[0]
    # a pin already in touched is somebody else's line to report
    assert cpc.unexplained_pins(lint, {"zz_o"}, old, new) == []


def _git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", *args], cwd=repo, check=True,
                          capture_output=True, text=True).stdout


@pytest.mark.skipif(shutil.which("verilator") is None, reason="verilator not on PATH")
def test_end_to_end_unpacked_array_port_breaks_its_consumer(tmp_path: Path):
    repo = tmp_path / "repo"
    comp = repo / "projects" / "components" / "x"
    (comp / "rtl").mkdir(parents=True)
    (comp / "dv" / "tb").mkdir(parents=True)
    (comp / "filelists").mkdir()
    mod = comp / "rtl" / "leaf.sv"
    tb = comp / "dv" / "tb" / "leaf_tb_top.sv"
    mod.write_text(textwrap.dedent("""\
        module leaf #(parameter int NUM_BANKS = 2) (
            input  logic clk,
            output logic plain_o
        );
            assign plain_o = clk;
        endmodule
        """))
    tb.write_text(textwrap.dedent("""\
        module leaf_tb_top (input logic clk, output logic plain_o);
            leaf u_leaf (.clk(clk), .plain_o(plain_o));
        endmodule
        """))
    (comp / "filelists" / "leaf_tb_top.f").write_text(
        f"{mod.relative_to(repo).as_posix()}\n{tb.relative_to(repo).as_posix()}\n")
    _git(repo, "init", "-q")
    _git(repo, "-c", "user.email=t@t", "-c", "user.name=t", "add", ".")
    _git(repo, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-q", "-m", "base")

    # the change: an UNPACKED-array output; the consumer is NOT updated
    mod.write_text(mod.read_text().replace(
        "    output logic plain_o\n",
        "    output logic plain_o,\n    output logic [31:0] stat_o [NUM_BANKS]\n").replace(
        "    assign plain_o = clk;\n",
        "    assign plain_o = clk;\n    always_comb for (int i = 0; i < NUM_BANKS; i++) stat_o[i] = 32'(i);\n"))
    env = dict(os.environ)
    r = subprocess.run([sys.executable, str(CHECKER), mod.relative_to(repo).as_posix()],
                       cwd=repo, capture_output=True, text=True, env=env)
    assert r.returncode == 1, f"the checker passed a consumer missing an unpacked-array pin:\n{r.stderr}"
    assert "'stat_o'" in r.stderr and "leaf_tb_top" in r.stderr

    # the consumer connects the pin: clean
    tb.write_text(tb.read_text().replace(".plain_o(plain_o)", ".plain_o(plain_o), .stat_o()"))
    r = subprocess.run([sys.executable, str(CHECKER), mod.relative_to(repo).as_posix()],
                       cwd=repo, capture_output=True, text=True, env=env)
    assert r.returncode == 0, r.stderr
