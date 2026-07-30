# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.tests.test_toolchain
# Purpose: Round-trip generated RTL through verilator and yosys
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Toolchain round-trip tests.

Every construct the generator can emit is built here and pushed through
``verilator --lint-only`` and a ``yosys`` synthesis check. Rendering tests prove
the output *looks* right; these prove it *is* right -- that it elaborates, has
no width or driver errors, and maps to hardware.

The modules below are rebuilt from the repo's condensed LRM, so this doubles as
a statement of the SystemVerilog subset the library is expected to cover.
"""

from __future__ import annotations

import pytest

from svsherpa import (
    B,
    C,
    Case,
    Concat,
    GenFor,
    GenIf,
    If,
    Instance,
    Module,
    ONES,
    Repl,
    ResetSpec,
    AlwaysComb,
    AlwaysFF,
    Struct,
    ZERO,
    clog2,
    mux,
    verify,
)

pytestmark = pytest.mark.toolchain


# ---------------------------------------------------------------------------
# builders, one per LRM construct group
# ---------------------------------------------------------------------------
def build_operators() -> Module:
    """Arithmetic, relational, equality, logical, bitwise, shift, reduction."""
    m = Module("verilog_operators", purpose="Operator coverage")
    a, b = m.input("a", 8), m.input("b", 8)
    sel = m.input("sel", 4)
    outs = {
        "a_plus_b": a + b,
        "a_minus_b": a - b,
        "a_dividedby_b": a // b,
        "a_modulo_b": a % b,
        "not_a_bitwise": ~a,
        "a_or_b_bitwise": a | b,
        "a_and_b_bitwise": a & b,
        "a_xor_b_bitwise": a ^ b,
        "a_nor_b_bitwise": ~(a | b),
        "a_nand_b_bitwise": ~(a & b),
        "data_shift_rt": a >> 3,
        "data_shift_lt": a << 4,
    }
    bits = {
        "a_lessthan_b": a < b,
        "a_greaterthan_b": a > b,
        "a_lessthanorequal_b": a <= b,
        "a_greaterthanorequal_b": a >= b,
        "a_equalxz_b": a.eqx(b),
        "a_notequalxz_b": a.nex(b),
        "a_equalu_b": a == b,
        "a_notequalu_b": a != b,
        "a_and_b": a.ror().land(b.ror()),
        "a_or_b": a.ror().lor(b.ror()),
        "not_a": a.rnor(),
        "any_sel_hi": sel.ror(),
        "all_sel_hi": sel.rand(),
        "sel_parity": sel.rxor(),
        "inv_sel_parity": sel.rxnor(),
        "inv_any_sel_hi": sel.rnor(),
        "inv_all_sel_hi": sel.rnand(),
    }
    product = m.logic("product", 16)
    m.assign(product, a * b)
    m.assign(m.output("a_times_b", 8), product[7:0])
    for name, expr in outs.items():
        m.assign(m.output(name, 8), expr)
    for name, expr in bits.items():
        m.assign(m.output(name), expr)
    return m


def build_case_mux() -> Module:
    """A case-based mux, including a multi-line arm."""
    m = Module("case_mux", purpose="Case mux")
    a, b, c = m.input("a", 3), m.input("b", 3), m.input("c", 3)
    sel = m.input("sel", 2)
    out = m.output("out", 3)
    m.always_comb(Case(sel,
                       (B(0, 2), out.set(a)),
                       (B(1, 2), out.set(b)),
                       (B(2, 2), out[2].set(c[2]), out[1].set(c[1]),
                        out[0].set(c[0])),
                       default=out.set(ZERO)))
    return m


def build_case_variants() -> Module:
    """`unique case` and one-hot `priority case`."""
    m = Module("case_variants", purpose="unique and priority case")
    sel = m.input("sel", 2)
    a, b, c = m.input("a", 8), m.input("b", 8), m.input("c", 8)
    uniq = m.output("out_unique", 8)
    prio = m.output("out_priority", 8)
    m.always_comb(Case(sel,
                       (B(0, 2), uniq.set(a)),
                       (B(1, 2), uniq.set(b)),
                       (B(2, 2), uniq.set(c)),
                       default=uniq.set(ZERO),
                       kind="unique case"))
    m.always_comb(Case(C(1, 1, base="b"),
                       (sel[0], prio.set(a)),
                       (sel[1], prio.set(b)),
                       default=prio.set(ZERO),
                       kind="priority case"))
    return m


def build_moore_binary() -> Module:
    """Moore FSM, binary encoded, two-block style."""
    m = Module("MooreFSM_4State", purpose="Moore FSM, binary")
    clk, rst = m.input("clk"), m.input("rst_n")
    s0, s1, s2 = m.output("state0"), m.output("state1"), m.output("state2")
    st = m.enum("states_fsm_t", ["S0", "S1", "S2", "S3"])
    state = m.logic("state", st)
    m.always_ff(clk, rst, reset=[state.set(st.S0)],
                body=[Case(state,
                           (st.S0, state.set(st.S1)),
                           (st.S1, state.set(st.S2)),
                           (st.S2, state.set(st.S3)),
                           (st.S3, state.set(st.S0)),
                           default=state.set(st.S0))],
                comment="State register")
    m.always_comb(s0.set(ZERO), s1.set(ZERO), s2.set(ZERO),
                  Case(state,
                       (st.S0, s0.set(ONES)),
                       (st.S1, s1.set(ONES)),
                       (st.S2, s2.set(ONES)),
                       (st.S3,),
                       default=None),
                  comment="Output decode -- current state only")
    return m


def build_mealy() -> Module:
    """Mealy FSM: outputs depend on state and input."""
    m = Module("MealyFSM_4State", purpose="Mealy FSM")
    clk, rst = m.input("clk"), m.input("rst_n")
    trigger = m.input("input_signal")
    s0, s1, s2 = m.output("state0"), m.output("state1"), m.output("state2")
    st = m.enum("states_fsm_t", ["S0", "S1", "S2", "S3"])
    cur = m.logic("current_state", st)
    nxt = m.logic("next_state", st)
    m.always_ff(clk, rst, reset=[cur.set(st.S0)], body=[cur.set(nxt)],
                comment="State register")
    m.always_comb(
        nxt.set(st.S0), s0.set(ZERO), s1.set(ZERO), s2.set(ZERO),
        Case(cur,
             (st.S0, nxt.set(mux(trigger, st.S1, st.S0)), s0.set(ONES)),
             (st.S1, nxt.set(mux(trigger, st.S2, st.S0)), s1.set(ONES)),
             (st.S2, nxt.set(mux(trigger, st.S3, st.S0)), s2.set(ONES)),
             (st.S3, nxt.set(st.S0)),
             default=nxt.set(st.S0)),
        comment="Next-state and output logic",
    )
    return m


def build_fifo_hsk() -> Module:
    """Sync FIFO with a valid/ready handshake and an inferred memory."""
    m = Module("SyncFIFO_Hsk", purpose="Sync FIFO, valid/ready")
    depth = m.param("DEPTH", 8)
    dw = m.param("DATA_WIDTH", 8)
    clk, rst = m.input("clk"), m.input("rst_n")
    wr_valid = m.input("wr_valid")
    wr_ready = m.output("wr_ready")
    wr_data = m.input("wr_data", dw)
    rd_valid = m.output("rd_valid")
    rd_ready = m.input("rd_ready")
    rd_data = m.output("rd_data", dw)

    pw = m.localparam("PW", clog2(depth) + 1, comment="pointer width + wrap bit")
    mem = m.mem("mem", dw, depth)
    wp, rp = m.logic("wp", pw), m.logic("rp", pw)
    wr_hsk, rd_hsk = m.wire("wr_hsk"), m.wire("rd_hsk")
    addr = clog2(depth)

    m.assign(wr_hsk, wr_valid.land(wr_ready))
    m.assign(rd_hsk, rd_valid.land(rd_ready))
    m.assign(wr_ready, (wp[pw - 1] == rp[pw - 1]).lor(wp[pw - 2:0] != rp[pw - 2:0]))
    m.assign(rd_valid, wp != rp)
    m.assign(rd_data, mem[rp[addr - 1:0]])
    m.always_ff(clk, rst,
                reset=[wp.set(ZERO), rp.set(ZERO)],
                body=[wp.set(wp + wr_hsk.cast(pw)),
                      rp.set(rp + rd_hsk.cast(pw))])
    m.always_ff(clk, body=[If(wr_hsk, mem[wp[addr - 1:0]].set(wr_data))],
                comment="Write port")
    return m


def build_rr_arbiter() -> Module:
    """Round-robin arbiter with a thermometer mask."""
    m = Module("rr_arbiter", purpose="Round-robin arbiter")
    n = m.param("N", 4)
    clk, rst = m.input("clk"), m.input("rst_n")
    req = m.input("req", n)
    gnt = m.output("gnt", n)
    mask = m.logic("mask", n)
    gnt_masked = m.logic("gnt_masked", n)
    gnt_unmasked = m.logic("gnt_unmasked", n)

    m.assign(gnt_masked, (req & mask) & ~((req & mask) - 1))
    m.assign(gnt_unmasked, req & ~(req - 1))
    m.assign(gnt, mux(gnt_masked.ror(), gnt_masked, gnt_unmasked))
    m.always_ff(clk, rst,
                reset=[mask.set(ONES)],
                body=[If(gnt.ror(), mask.set(~((gnt << 1) - 1)))])
    return m


def build_gen_blocks() -> Module:
    """GenIf choosing between a registered and a combinatorial path."""
    m = Module("gen_blocks", purpose="Registered or pass-through")
    width = m.param("WIDTH", 8)
    use_flop = m.param("USE_FLOP", 1, "bit")
    clk, rst = m.input("clk"), m.input("rst_n")
    d, q = m.input("d", width), m.output("q", width)
    m.add(GenIf(use_flop, label="g_registered",
                body=[AlwaysFF(clk, q.set(d), reset=ResetSpec(rst),
                               reset_body=[q.set(ZERO)])],
                else_label="g_combinatorial",
                else_body=[AlwaysComb(q.set(d))],
                wrap=True))
    return m


def build_gen_ff_array() -> Module:
    """GenFor replicating a flop bank across a packed 2-D port."""
    m = Module("gen_ff_array", purpose="Per-channel flop bank")
    channels = m.param("CHANNELS", 4)
    width = m.param("WIDTH", 8)
    clk, rst = m.input("clk"), m.input("rst_n")
    en = m.input("en", channels)
    d = m.input("d", [channels, width])
    q = m.output("q", [channels, width])
    m.add(GenFor("i", channels, label="g_ch", wrap=True, body=lambda i: [
        AlwaysFF(clk, If(en[i], q[i].set(d[i])),
                 reset=ResetSpec(rst), reset_body=[q[i].set(ZERO)]),
    ]))
    return m


def build_gen_module_array(child: Module) -> Module:
    """GenFor instantiating a parameterised sub-module N times."""
    m = Module("gen_module_array", purpose="Bank of FIFO lanes")
    lanes = m.param("NUM_LANES", 4)
    dw = m.param("DATA_WIDTH", 16)
    fd = m.param("FIFO_DEPTH", 8)
    clk, rst = m.input("clk"), m.input("rst_n")
    wv, wr = m.input("wr_valid", lanes), m.output("wr_ready", lanes)
    wd = m.input("wr_data", [lanes, dw])
    rv, rr = m.output("rd_valid", lanes), m.input("rd_ready", lanes)
    rd = m.output("rd_data", [lanes, dw])
    m.add(GenFor("i", lanes, label="g_lane", wrap=True, body=lambda i: [
        Instance("", "u_fifo", of=child,
                 params={"DEPTH": fd, "DATA_WIDTH": dw},
                 ports={"clk": clk, "rst_n": rst,
                        "wr_valid": wv[i], "wr_ready": wr[i], "wr_data": wd[i],
                        "rd_valid": rv[i], "rd_ready": rr[i], "rd_data": rd[i]}),
    ]))
    return m


def build_struct_example() -> Module:
    """Packed struct through a register, with field access."""
    m = Module("struct_example", purpose="Packed struct pipeline stage")
    cmd_t = m.struct("cmd_pkt_t", [("valid", 1), ("opcode", 3),
                                   ("addr", 12), ("data", 16)])
    clk, rst = m.input("clk"), m.input("rst_n")
    cmd_in = m.input("cmd_in", cmd_t)
    cmd_out = m.output("cmd_out", cmd_t)
    cmd_q = m.logic("cmd_q", cmd_t)
    m.always_ff(clk, rst, reset=[cmd_q.set(ZERO)], body=[cmd_q.set(cmd_in)])
    m.always_comb(
        cmd_out.set(cmd_q),
        cmd_out.valid.set(cmd_q.valid & (cmd_q.opcode != B(0b111, 3))),
    )
    return m


def build_concat_repl() -> Module:
    """Concatenation, replication and fills."""
    m = Module("concat_repl", purpose="Concat and replicate")
    width = m.param("WIDTH", 8)
    a = m.input("a", width)
    swapped = m.output("swapped", width)
    doubled = m.output("doubled", 2 * width)
    zeroed = m.output("zeroed", width)
    m.assign(swapped, Concat(a[0], a[width - 1:1]))
    m.assign(doubled, Repl(2, a))
    m.assign(zeroed, ZERO)
    return m


FIFO = build_fifo_hsk()

BUILDERS = {
    "operators": build_operators,
    "case_mux": build_case_mux,
    "case_variants": build_case_variants,
    "moore_binary": build_moore_binary,
    "mealy": build_mealy,
    "fifo_hsk": build_fifo_hsk,
    "rr_arbiter": build_rr_arbiter,
    "gen_blocks": build_gen_blocks,
    "gen_ff_array": build_gen_ff_array,
    "struct_example": build_struct_example,
    "concat_repl": build_concat_repl,
    "gen_module_array": lambda: build_gen_module_array(FIFO),
}


# ---------------------------------------------------------------------------
# tests
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("name", sorted(BUILDERS))
def test_lints_and_synthesises(name, has_verilator, has_yosys):
    """Each LRM construct must lint and synthesise cleanly."""
    if not (has_verilator or has_yosys):
        pytest.skip("no SV toolchain available")
    module = BUILDERS[name]()
    if name == "gen_module_array":
        # An instance needs its child in the same compilation unit.
        combined = FIFO.emit() + "\n" + module.emit()
        report = verify(combined, lint=True, synth=False)
    else:
        report = verify(module, lint=True, synth=True)
    assert report.ok, f"{name}:\n{report}"


@pytest.mark.parametrize("name", sorted(BUILDERS))
def test_no_unexpected_warnings(name):
    """The generator's own checks must be quiet on known-good designs."""
    module = BUILDERS[name]()
    noisy = [
        w for w in module.check()
        if w.kind in ("width", "latch")
    ]
    assert not noisy, f"{name}: {[str(w) for w in noisy]}"


def test_report_renders_failures_readably():
    broken = "module oops (input logic a); assign a = 1'b0; endmodule"
    report = verify(broken, synth=False)
    assert not report.ok
    assert "verilator" in str(report)


def test_verify_accepts_raw_text():
    good = (
        "`timescale 1ns / 1ps\n"
        "module tiny (input logic a, output logic y);\n"
        "    assign y = ~a;\n"
        "endmodule : tiny\n"
    )
    report = verify(good, synth=False)
    assert report.ok, str(report)


def test_missing_tool_is_skipped_not_failed(monkeypatch):
    import svsherpa.tools as tools

    monkeypatch.setattr(tools.shutil, "which", lambda _: None)
    result = tools.verilator_lint("module m; endmodule")
    assert result.status == "skipped"
    assert result.ok
