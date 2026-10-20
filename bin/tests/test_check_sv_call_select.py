# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Tests for bin/check_sv_call_select.py.

The check exists because Verilator accepts `f(x)[0]` silently and Vivado
refuses it (vault/handbook/design/select-on-function-call.md). A check that
reports nothing on the whole tree proves nothing on its own, so:

  * every shape that IS a select on a call is pinned as found, including the
    one that reached Vivado (axi_stress_mst_rd, 2026-10-19), a system function,
    a call spread over lines and whitespace before the bracket;
  * every near miss is pinned as clean: a select inside the call's arguments,
    a width cast of a call, control flow, macros, named ports, parameter lists,
    instance arrays, comments and strings;
  * the command line returns 1 on a finding and 0 on a clean file.
"""
from __future__ import annotations

import importlib.util
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

BIN = Path(__file__).resolve().parents[1]
_spec = importlib.util.spec_from_file_location('ccs', BIN / 'check_sv_call_select.py')
ccs = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ccs)


def hits(src: str) -> list:
    return ccs.find(ccs.strip_comments_and_strings(textwrap.dedent(src)))


@pytest.mark.parametrize('src', [
    "assign w = f_sb(t_addr ^ 32'h7F4A_7C15, cfg_hash_seed)[0];",
    "assign w = f(x)[7:0];",
    "assign w = f(x) [3];",
    "assign w = $clog2(N)[1:0];",
    "assign w = a & g(h(x), y)[2];",
    """assign w = f_sb(t_addr,
                    cfg_hash_seed)[0];""",
])
def test_found(src: str) -> None:
    assert len(hits(src)) == 1, src


@pytest.mark.parametrize('src', [
    "assign w = f(x[3:0]);",
    "assign w = 8'(f(x));",
    "assign w = (a + b) & c;",
    "if (a) begin end",
    "case (sel) default: ; endcase",
    "assign m = `RST_ASSERTED(aresetn) ? a : b;",
    "foo u_foo (.a (b[3:0]), .c (d));",
    "foo #(.W (8)) u_foo (.a (b));",
    "foo u_arr [3:0] (.a (b));",
    "assign w = f(x); // f(x)[0] in a comment",
    'initial $display("f(x)[0]");',
    "/* f(x)[0] */ assign w = f(x);",
    "for (int i = 0; i < N; i++) a[i] = b[i];",
    "assign w = r_s_bsb[tb_lk_idx];",
])
def test_clean(src: str) -> None:
    assert hits(src) == [], src


def test_line_number() -> None:
    src = "module m;\n// f(x)[0]\nassign a = b;\nassign w = f(x)[1];\nendmodule\n"
    assert [ln for ln, _ in hits(src)] == [4]


def test_cli_exit_codes(tmp_path: Path) -> None:
    bad, good = tmp_path / 'bad.sv', tmp_path / 'good.sv'
    bad.write_text("module m; assign w = f(x)[0]; endmodule\n")
    good.write_text("module m; logic [7:0] h; assign h = f(x); assign w = h[0]; endmodule\n")
    run = [sys.executable, str(BIN / 'check_sv_call_select.py')]
    r = subprocess.run(run + [str(bad)], capture_output=True, text=True)
    assert r.returncode == 1 and 'bad.sv:1:' in r.stdout
    r = subprocess.run(run + [str(good)], capture_output=True, text=True)
    assert r.returncode == 0, r.stdout
