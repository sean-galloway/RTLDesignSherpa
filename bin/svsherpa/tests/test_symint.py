# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.tests.test_symint
# Purpose: Width algebra -- normalisation, evaluation, rendering
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Tests for the symbolic width algebra."""

from __future__ import annotations

import pytest

from svsherpa.errors import SvError
from svsherpa.symint import SymInt, widths_conflict


def test_literal_render_and_eval():
    assert SymInt.lit(8).render() == "8"
    assert SymInt.lit(8).try_eval({}) == 8
    assert SymInt.lit(8).is_const()


def test_param_arithmetic_renders_like_sv():
    width = SymInt.ref("WIDTH")
    assert (width - 1).render() == "WIDTH-1"
    assert (width + 1).render() == "WIDTH+1"
    assert (2 * width).render() == "2*WIDTH"
    assert (2 * width - 1).render() == "2*WIDTH-1"


def test_normalisation_makes_equal_widths_compare_equal():
    """(WIDTH-1)+1 is WIDTH -- this is what stops false width warnings."""
    width = SymInt.ref("WIDTH")
    assert (width - 1) + 1 == width
    assert width + 0 == width
    assert (width * 2) == (2 * width)


def test_terms_cancel_to_a_constant():
    width = SymInt.ref("WIDTH")
    assert (width - width) == SymInt.lit(0)
    assert (width - width).is_const()


def test_eval_needs_every_atom_bound():
    expr = SymInt.ref("A") * SymInt.ref("B")
    assert expr.try_eval({"A": 2}) is None
    assert expr.try_eval({"A": 2, "B": 3}) == 6


def test_clog2_folds_when_constant():
    assert SymInt.clog2(8).try_eval({}) == 3
    assert SymInt.clog2(9).try_eval({}) == 4
    assert SymInt.clog2(1).try_eval({}) == 0


def test_clog2_stays_symbolic_when_unknown():
    expr = SymInt.clog2(SymInt.ref("DEPTH"))
    assert expr.render() == "$clog2(DEPTH)"
    assert expr.try_eval({}) is None


def test_clog2_plus_one_is_the_fifo_pointer_width():
    pw = SymInt.clog2(SymInt.ref("DEPTH")) + 1
    assert pw.render() == "$clog2(DEPTH)+1"


def test_product_of_params_renders_sorted_and_stable():
    lhs = SymInt.ref("CHANNELS") * SymInt.ref("WIDTH")
    rhs = SymInt.ref("WIDTH") * SymInt.ref("CHANNELS")
    assert lhs == rhs


def test_render_parenthesises_when_context_demands():
    width = SymInt.ref("WIDTH")
    assert (width - 1).render(prec=100) == "(WIDTH-1)"
    assert width.render(prec=100) == "WIDTH"


def test_bool_is_rejected_as_a_width():
    with pytest.raises(SvError, match="bool"):
        SymInt.lit(1) + True


def test_non_numeric_is_rejected_as_a_width():
    with pytest.raises(SvError, match="as a width"):
        SymInt.lit(1) + "eight"


@pytest.mark.parametrize(
    "lhs, rhs, env, expected",
    [
        (SymInt.lit(8), SymInt.lit(4), {}, True),
        (SymInt.lit(8), SymInt.lit(8), {}, False),
        (SymInt.ref("A"), SymInt.ref("B"), {}, False),          # unprovable
        (SymInt.ref("A"), SymInt.ref("B"), {"A": 8, "B": 4}, True),
        (SymInt.ref("A"), SymInt.ref("A"), {}, False),
    ],
)
def test_widths_conflict_only_reports_provable_mismatches(lhs, rhs, env, expected):
    assert widths_conflict(lhs, rhs, env) is expected


def test_negation():
    assert (-SymInt.lit(5)).try_eval({}) == -5
