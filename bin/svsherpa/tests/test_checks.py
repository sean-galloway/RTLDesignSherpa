# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.tests.test_checks
# Purpose: The static checks -- drivers, widths, latches, unused signals
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Tests for the static checks.

These are the reason to use a generator rather than a template: each of these
mistakes is one an experienced engineer still makes at 5pm, and each is caught
at build time with the signal named.
"""

from __future__ import annotations

import pytest

from svsherpa import B, C, Case, If, Module, ONES, ZERO
from svsherpa.errors import SvError


def kinds(module) -> set[str]:
    return {w.kind for w in module.check()}


# ----------------------------------------------------------------- drivers
def test_two_drivers_is_an_error():
    m = Module("dd")
    clk, rst = m.input("clk"), m.input("rst_n")
    q = m.output("q")
    m.assign(q, C(0))
    m.always_ff(clk, rst, reset=[q.set(ZERO)], body=[q.set(ONES)])
    with pytest.raises(SvError, match="exactly one driver"):
        m.check()


def test_reset_and_body_driving_one_register_is_fine():
    """The classic false positive: one register, two arms, one driver."""
    m = Module("single")
    clk, rst = m.input("clk"), m.input("rst_n")
    q = m.output("q", 8)
    m.always_ff(clk, rst, reset=[q.set(ZERO)], body=[q.set(ONES)])
    assert "exactly one driver" not in " ".join(str(w) for w in m.check())


def test_assigning_an_input_is_an_error():
    m = Module("di")
    a = m.input("a")
    m.assign(a, C(0))
    with pytest.raises(SvError, match="input port"):
        m.check()


def test_undriven_output_is_warned():
    m = Module("floating")
    m.input("a")
    m.output("y")
    assert "undriven-output" in kinds(m)


# ------------------------------------------------------------------ widths
def test_truncating_assignment_is_warned():
    m = Module("trunc")
    a = m.input("a", 8)
    y = m.output("y", 4)
    m.assign(y, a)
    warnings = [str(w) for w in m.check()]
    assert any("truncates" in w and "8 bits" in w for w in warnings)


def test_widening_assignment_is_warned():
    m = Module("widen")
    a = m.input("a", 4)
    y = m.output("y", 8)
    m.assign(y, a)
    assert any("zero-extends" in str(w) for w in m.check())


def test_matching_widths_are_silent():
    m = Module("exact")
    a = m.input("a", 8)
    y = m.output("y", 8)
    m.assign(y, a)
    assert "width" not in kinds(m)


def test_symbolic_widths_that_normalise_equal_are_silent():
    """`WIDTH-1` down to a `[WIDTH-2:0]` target must not warn."""
    m = Module("symbolic")
    width = m.param("WIDTH", 8)
    a = m.input("a", width)
    y = m.output("y", width - 1)
    m.assign(y, a[width - 2:0])
    assert "width" not in kinds(m)


def test_different_params_are_not_assumed_to_conflict():
    """A and B may be equal at elaboration; do not cry wolf."""
    m = Module("twoparams")
    a_w = m.param("A_WIDTH", 8)
    b_w = m.param("B_WIDTH", 8)
    a = m.input("a", a_w)
    y = m.output("y", b_w)
    m.assign(y, a)
    assert "width" not in kinds(m)


def test_fill_literals_never_warn():
    m = Module("fills")
    y = m.output("y", 8)
    m.assign(y, ZERO)
    assert "width" not in kinds(m)


def test_oversized_unsized_literal_is_warned():
    m = Module("toobig")
    y = m.output("y", 2)
    m.assign(y, C(255))
    assert any("needs 8 bits" in str(w) for w in m.check())


def test_memory_index_yields_the_word_width():
    """Indexing an unpacked memory gives the packed word, not one bit."""
    m = Module("memwidth")
    dw = m.param("DATA_WIDTH", 8)
    depth = m.param("DEPTH", 16)
    mem = m.mem("mem", dw, depth)
    addr = m.input("addr", 4)
    y = m.output("y", dw)
    m.assign(y, mem[addr])
    assert "width" not in kinds(m)


# ------------------------------------------------------------------ latches
def test_incomplete_if_in_always_comb_is_warned():
    m = Module("latchy")
    a, b = m.input("a"), m.input("b")
    y = m.output("y")
    m.always_comb(If(a, y.set(b)))
    assert "latch" in kinds(m)


def test_default_assignment_first_clears_the_latch_warning():
    """The standard fix: assign a default, then override conditionally."""
    m = Module("defaulted")
    a, b = m.input("a"), m.input("b")
    y = m.output("y")
    m.always_comb(y.set(ZERO), If(a, y.set(b)))
    assert "latch" not in kinds(m)


def test_complete_if_else_has_no_latch():
    m = Module("complete")
    a, b = m.input("a"), m.input("b")
    y = m.output("y")
    m.always_comb(If(a, y.set(b)).Else(y.set(ZERO)))
    assert "latch" not in kinds(m)


def test_case_without_default_is_warned():
    m = Module("casey")
    sel = m.input("sel", 2)
    a = m.input("a", 8)
    y = m.output("y", 8)
    m.always_comb(Case(sel, (B(0, 2), y.set(a))))
    assert "latch" in kinds(m)


def test_case_with_default_is_clean():
    m = Module("casedefault")
    sel = m.input("sel", 2)
    a = m.input("a", 8)
    y = m.output("y", 8)
    m.always_comb(Case(sel, (B(0, 2), y.set(a)), default=y.set(ZERO)))
    assert "latch" not in kinds(m)


def test_always_ff_is_not_latch_checked():
    """A clocked block holding its value is a register, which is the point."""
    m = Module("ffhold")
    clk, rst, en = m.input("clk"), m.input("rst_n"), m.input("en")
    q = m.output("q", 8)
    a = m.input("a", 8)
    m.always_ff(clk, rst, reset=[q.set(ZERO)], body=[If(en, q.set(a))])
    assert "latch" not in kinds(m)


# ------------------------------------------------------------------- unused
def test_unused_signal_is_warned():
    m = Module("orphaned")
    a = m.input("a")
    y = m.output("y")
    m.logic("never_used", 4)
    m.assign(y, a)
    assert "unused-signal" in kinds(m)


def test_used_signal_is_not_warned():
    m = Module("tidy")
    a = m.input("a", 8)
    y = m.output("y", 8)
    mid = m.logic("mid", 8)
    m.assign(mid, a)
    m.assign(y, mid)
    assert "unused-signal" not in kinds(m)


# -------------------------------------------------------------- empty blocks
def test_empty_always_comb_is_rejected():
    m = Module("emptycomb")
    with pytest.raises(SvError, match="empty"):
        m.always_comb()


def test_empty_always_ff_is_rejected():
    m = Module("emptyff")
    clk = m.input("clk")
    with pytest.raises(SvError, match="empty"):
        m.always_ff(clk)


def test_reset_body_without_a_reset_signal_is_rejected():
    from svsherpa import AlwaysFF

    m = Module("noreset")
    clk = m.input("clk")
    q = m.output("q")
    with pytest.raises(SvError, match="no reset signal"):
        AlwaysFF(clk, q.set(ZERO), reset_body=[q.set(ZERO)])


def test_unknown_reset_style_is_rejected():
    from svsherpa import ResetSpec

    with pytest.raises(SvError, match="unknown reset style"):
        ResetSpec(style="sideways")
