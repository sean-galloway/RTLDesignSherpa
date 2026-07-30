# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.tests.test_expr
# Purpose: Expression rendering, precedence and width inference
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Tests for expression rendering and width inference.

The rendering tests are the contract with the reader: generated SV has to look
like SV a person would write, so exact-string assertions are appropriate here.
"""

from __future__ import annotations

import pytest

from svsherpa import (
    B,
    C,
    Concat,
    Logic,
    ONES,
    Param,
    Repl,
    ZERO,
    clog2,
    mux,
    same,
)
from svsherpa.errors import SvError


@pytest.fixture
def ab():
    return Logic("a", 8), Logic("b", 8)


# --------------------------------------------------------------- operators
@pytest.mark.parametrize(
    "build, expected",
    [
        (lambda a, b: a + b, "a + b"),
        (lambda a, b: a - b, "a - b"),
        (lambda a, b: a * b, "a * b"),
        (lambda a, b: a % b, "a % b"),
        (lambda a, b: a ** b, "a ** b"),
        (lambda a, b: a & b, "a & b"),
        (lambda a, b: a | b, "a | b"),
        (lambda a, b: a ^ b, "a ^ b"),
        (lambda a, b: ~a, "~a"),
        (lambda a, b: a << 4, "a << 4"),
        (lambda a, b: a >> 8, "a >> 8"),
        (lambda a, b: a < b, "a < b"),
        (lambda a, b: a >= b, "a >= b"),
        (lambda a, b: a == b, "a == b"),
        (lambda a, b: a != b, "a != b"),
        (lambda a, b: a.eqx(b), "a === b"),
        (lambda a, b: a.nex(b), "a !== b"),
        (lambda a, b: a.lnot(), "!a"),
    ],
)
def test_operator_rendering_matches_sv(ab, build, expected):
    a, b = ab
    assert build(a, b).render() == expected


@pytest.mark.parametrize(
    "method, expected",
    [
        ("ror", "|a"),
        ("rand", "&a"),
        ("rxor", "^a"),
        ("rnor", "~|a"),
        ("rnand", "~&a"),
        ("rxnor", "~^a"),
    ],
)
def test_reduction_operators(ab, method, expected):
    a, _ = ab
    assert getattr(a, method)().render() == expected


def test_logical_operators_parenthesise_comparisons(ab):
    """House style: `(a == b) || (c != d)`, not bare precedence."""
    a, b = ab
    c, d = Logic("c", 8), Logic("d", 8)
    assert (a == b).lor(c != d).render() == "(a == b) || (c != d)"
    assert (a == b).land(c != d).render() == "(a == b) && (c != d)"


def test_bitwise_nor_gets_explicit_parens(ab):
    """`~(a | b)` must not degrade to `~a | b`, nor collide with `~|`."""
    a, b = ab
    assert (~(a | b)).render() == "~(a | b)"
    assert (~(a & b)).render() == "~(a & b)"


def test_precedence_avoids_redundant_parens(ab):
    a, b = ab
    c = Logic("c", 8)
    assert ((a + b) * c).render() == "(a + b) * c"
    assert (a + b * c).render() == "a + b * c"


def test_subtraction_keeps_right_hand_parens(ab):
    a, b = ab
    c = Logic("c", 8)
    assert (a - (b - c)).render() == "a - (b - c)"


# ------------------------------------------------------------------ widths
def test_arithmetic_takes_the_wider_operand():
    assert (Logic("a", 8) + Logic("b", 4)).width.try_eval({}) == 8


def test_multiply_is_full_precision():
    assert (Logic("a", 8) * Logic("b", 8)).width.try_eval({}) == 16


def test_comparison_is_one_bit(ab):
    a, b = ab
    assert (a == b).width.try_eval({}) == 1
    assert a.ror().width.try_eval({}) == 1


def test_shift_keeps_left_width(ab):
    a, _ = ab
    assert (a << 3).width.try_eval({}) == 8


def test_concat_width_is_the_sum():
    node = Concat(Logic("a", 8), Logic("b", 4), Logic("c", 1))
    assert node.width.try_eval({}) == 13
    assert node.render() == "{a, b, c}"


def test_repl_width_multiplies():
    node = Repl(4, Logic("a", 2))
    assert node.width.try_eval({}) == 8
    assert node.render() == "{4{a}}"


def test_repl_parenthesises_compound_counts():
    """`{WIDTH-1{1'b0}}` is a parse hazard; the parens are mandatory."""
    width = Param("WIDTH", 8)
    assert Repl(width - 1, C(0, 1, base="b")).render() == "{(WIDTH-1){1'b0}}"


def test_part_select_keeps_sv_descending_order():
    """`sig[WIDTH-2:0]` in Python emits the same text, not Python slice order."""
    width = Param("WIDTH", 8)
    sig = Logic("data", width)
    node = sig[width - 2:0]
    assert node.render() == "data[WIDTH-2:0]"
    assert node.width.try_eval({"WIDTH": 8}) == 7


def test_part_select_width_is_msb_minus_lsb_plus_one():
    sig = Logic("data", 16)
    assert sig[7:0].width.try_eval({}) == 8
    assert sig[15:8].width.try_eval({}) == 8


def test_bit_select_is_one_bit():
    sig = Logic("data", 16)
    assert sig[3].render() == "data[3]"
    assert sig[3].width.try_eval({}) == 1


def test_part_select_rejects_a_step():
    with pytest.raises(SvError, match="step"):
        _ = Logic("d", 8)[7:0:2]


# ---------------------------------------------------------------- literals
def test_sized_and_unsized_literals():
    assert C(0).render() == "0"
    assert C(255, 8).render() == "8'hff"
    assert B(0b10, 2).render() == "2'b10"
    assert C(5, 8, base="d").render() == "8'd5"


def test_fill_literals_are_width_agnostic():
    assert ZERO.render() == "'0"
    assert ONES.render() == "'1"


def test_cast_renders_as_sized_cast():
    width = Param("WIDTH", 8)
    assert C(3).cast(width - 1).render() == "(WIDTH-1)'(3)"


def test_signed_helpers():
    a = Logic("a", 8)
    assert a.signed_().render() == "$signed(a)"
    assert a.unsigned_().render() == "$unsigned(a)"


def test_mux_renders_as_ternary(ab):
    a, b = ab
    sel = Logic("sel")
    assert mux(sel, a, b).render() == "sel ? a : b"


def test_nested_mux_parenthesises(ab):
    a, b = ab
    s0, s1 = Logic("s0"), Logic("s1")
    assert mux(s0, mux(s1, a, b), b).render() == "s0 ? (s1 ? a : b) : b"


def test_clog2_as_a_width_accepts_a_param():
    depth = Param("DEPTH", 8)
    assert clog2(depth).render() == "$clog2(DEPTH)"
    assert clog2(8).try_eval({}) == 3


# -------------------------------------------------------------- edge cases
def test_same_compares_structurally(ab):
    a, b = ab
    assert same(a + b, a + b)
    assert not same(a + b, b + a)


def test_eq_builds_an_expression_not_a_bool(ab):
    """`==` is the SV operator here; that is a deliberate Python wart."""
    a, b = ab
    assert not isinstance(a == b, bool)


def test_expressions_hash_by_identity(ab):
    a, _ = ab
    assert len({a, a}) == 1


def test_lifting_rejects_junk(ab):
    a, _ = ab
    with pytest.raises(SvError, match="in an expression"):
        _ = a + "four"
