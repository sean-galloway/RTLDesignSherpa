# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.tests.test_stmt
# Purpose: Statement rendering -- if/else chains, case, blocks, operators
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Tests for procedural statement rendering."""

from __future__ import annotations

import pytest

from svsherpa import B, Block, Case, Comment, If, Logic, ZERO
from svsherpa.errors import SvError
from svsherpa.stmt import EmitCtx


def render(stmt, op="=") -> str:
    return "\n".join(stmt.emit(EmitCtx(indent=0, op=op)))


@pytest.fixture
def sigs():
    return Logic("a", 8), Logic("b", 8), Logic("sel", 2), Logic("out", 8)


# ------------------------------------------------------------- assignment
def test_operator_comes_from_the_context(sigs):
    a, b, _, _ = sigs
    assert render(a.set(b), op="=") == "a = b;"
    assert render(a.set(b), op="<=") == "a <= b;"


# ---------------------------------------------------------------- if/else
def test_single_statement_branch_has_no_begin_end(sigs):
    a, b, _, out = sigs
    text = render(If(a, out.set(b)))
    assert text == "if (a)\n    out = b;"


def test_multi_statement_branch_gets_begin_end(sigs):
    a, b, _, out = sigs
    text = render(If(a, out.set(b), out.set(a)))
    assert text.splitlines()[0] == "if (a) begin"
    assert text.splitlines()[-1] == "end"


def test_else_chains_onto_a_bracketed_branch(sigs):
    a, b, _, out = sigs
    text = render(If(a, out.set(b), out.set(a)).Else(out.set(ZERO)))
    assert "end else" in text


def test_else_follows_a_bare_branch_on_its_own_line(sigs):
    a, b, _, out = sigs
    text = render(If(a, out.set(b)).Else(out.set(ZERO)))
    assert text == "if (a)\n    out = b;\nelse\n    out = '0;"


def test_elif_chain(sigs):
    a, b, sel, out = sigs
    text = render(If(a, out.set(b)).Elif(b, out.set(a)).Else(out.set(ZERO)))
    assert "else if (b)" in text
    assert text.count("else") == 2


def test_if_is_immutable_under_chaining(sigs):
    """Else returns a new object, so a partial conditional is reusable."""
    a, b, _, out = sigs
    base = If(a, out.set(b))
    with_else = base.Else(out.set(ZERO))
    assert base.is_complete() is False
    assert with_else.is_complete() is True


def test_elif_after_else_is_rejected(sigs):
    a, b, _, out = sigs
    with pytest.raises(SvError, match="Elif cannot follow Else"):
        If(a, out.set(b)).Else(out.set(ZERO)).Elif(b, out.set(a))


def test_double_else_is_rejected(sigs):
    a, b, _, out = sigs
    with pytest.raises(SvError, match="twice"):
        If(a, out.set(b)).Else(out.set(ZERO)).Else(out.set(ZERO))


# ------------------------------------------------------------------- case
def test_case_arms_are_aligned(sigs):
    a, b, sel, out = sigs
    text = render(Case(sel,
                       (B(0, 2), out.set(a)),
                       (B(1, 2), out.set(b)),
                       default=out.set(ZERO)))
    lines = text.splitlines()
    assert lines[0] == "case (sel)"
    assert lines[-1] == "endcase"
    # The colons line up because `default` is the longest label.
    assert "2'b00:   out = a;" in text
    assert "default: out = '0;" in text


def test_case_kind_is_written_as_sv_writes_it(sigs):
    a, _, sel, out = sigs
    for kind in ("unique case", "priority case", "casez"):
        text = render(Case(sel, (B(0, 2), out.set(a)), default=out.set(ZERO),
                           kind=kind))
        assert text.startswith(kind + " (sel)")


def test_case_folds_multiple_matches_onto_one_arm(sigs):
    a, _, sel, out = sigs
    text = render(Case(sel, ([B(0, 2), B(1, 2)], out.set(a)),
                       default=out.set(ZERO)))
    assert "2'b00, 2'b01:" in text


def test_empty_case_arm_renders_a_bare_semicolon(sigs):
    """`S3: ;` -- a deliberately empty arm, as in a Moore output decode."""
    a, _, sel, out = sigs
    text = render(Case(sel, (B(0, 2), out.set(a)), (B(3, 2),),
                       default=out.set(ZERO)))
    assert "2'b11:   ;" in text


def test_multi_statement_case_arm_gets_begin_end(sigs):
    a, b, sel, out = sigs
    text = render(Case(sel, (B(0, 2), out.set(a), out.set(b)),
                       default=out.set(ZERO)))
    assert "2'b00:   begin" in text


def test_case_completeness_tracks_default(sigs):
    a, _, sel, out = sigs
    assert Case(sel, (B(0, 2), out.set(a))).is_complete() is False
    assert Case(sel, (B(0, 2), out.set(a)),
                default=out.set(ZERO)).is_complete() is True


def test_bad_case_arm_is_rejected(sigs):
    _, _, sel, _ = sigs
    with pytest.raises(SvError, match="bad case arm"):
        Case(sel, "nonsense")


# ------------------------------------------------------------------ blocks
def test_labelled_block(sigs):
    a, b, _, out = sigs
    text = render(Block(out.set(a), label="g_thing"))
    assert text.splitlines()[0] == "begin : g_thing"


def test_comment_statement(sigs):
    assert render(Comment("note this")) == "// note this"


def test_nested_if_is_bracketed_to_kill_dangling_else(sigs):
    """A nested conditional always gets begin/end.

    Bare nesting is legal SV but creates the dangling-else ambiguity, where an
    ``else`` silently binds to the inner ``if``. Bracketing costs two lines and
    removes the class of bug.
    """
    a, b, _, out = sigs
    text = render(If(a, If(b, out.set(a)).Else(out.set(b))))
    assert text == (
        "if (a) begin\n"
        "    if (b)\n"
        "        out = a;\n"
        "    else\n"
        "        out = b;\n"
        "end"
    )


def test_non_statement_in_a_body_is_rejected(sigs):
    a, _, _, _ = sigs
    with pytest.raises(SvError, match="expected a statement"):
        If(a, "out = 1;")


def test_targets_are_collected_through_nesting(sigs):
    a, b, _, out = sigs
    other = Logic("other", 8)
    stmt = If(a, out.set(b)).Else(other.set(b))
    assert set(stmt.targets()) == {"out", "other"}
