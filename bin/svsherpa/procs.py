# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.procs
# Purpose: Procedural blocks -- always_comb, always_ff, continuous assign
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Procedural blocks.

The blocking/non-blocking choice belongs to the block, not the assignment, so
``sig.set(x)`` emits ``<=`` inside :class:`AlwaysFF` and ``=`` inside
:class:`AlwaysComb`. Getting that wrong is one of the most common RTL bugs;
here it is not expressible.

Reset style is a module-wide setting rather than a per-block decision, because
mixing styles inside one design is how reset bugs get in:

``macro``
    ``\\`ALWAYS_FF_RST(clk, rst_n, ...)`` -- the house style, polarity and
    sync/async selected at compile time by ``reset_defs.svh``.
``async_low`` / ``async_high``
    An explicit ``@(posedge clk or negedge rst_n)`` sensitivity list.
``sync_low`` / ``sync_high``
    ``@(posedge clk)`` with the reset tested inside.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from .errors import SvError
from .expr import Expr, Raw as RawExpr, lift
from .stmt import Case, EmitCtx, If, Stmt, _as_stmts

RESET_STYLES = ("macro", "async_low", "async_high", "sync_low", "sync_high")


@dataclass
class ResetSpec:
    """How a clocked block expresses its reset."""

    signal: Expr | None = None
    style: str = "macro"
    macro: str = "ALWAYS_FF_RST"
    use_rst_asserted: bool = False

    def __post_init__(self) -> None:
        if self.style not in RESET_STYLES:
            raise SvError(
                f"unknown reset style {self.style!r}; expected one of {RESET_STYLES}"
            )

    @property
    def active_low(self) -> bool:
        return self.style in ("macro", "async_low", "sync_low")

    def condition(self) -> Expr:
        """The expression that tests 'reset is asserted'."""
        if self.signal is None:
            raise SvError("reset condition requested with no reset signal")
        if self.use_rst_asserted:
            return RawExpr(f"`RST_ASSERTED({self.signal.render()})")
        return self.signal.lnot() if self.active_low else self.signal


class Proc(Stmt):
    """Base class for procedural blocks."""

    header: str = ""

    def body_stmts(self) -> tuple[Stmt, ...]:  # pragma: no cover - abstract
        return ()


@dataclass
class AlwaysComb(Proc):
    """``always_comb`` -- combinatorial logic, blocking assignment."""

    body: tuple[Stmt, ...]
    comment: str = ""

    def __init__(self, *body, comment: str = ""):
        self.body = _as_stmts(body)
        self.comment = comment
        if not self.body:
            raise SvError("always_comb block is empty")

    def body_stmts(self) -> tuple[Stmt, ...]:
        return self.body

    def targets(self) -> list[str]:
        return [t for s in self.body for t in s.targets()]

    def emit(self, ctx: EmitCtx) -> list[str]:
        inner = EmitCtx(
            indent=ctx.indent,
            op="=",
            tab=ctx.tab,
            env=ctx.env,
            warnings=ctx.warnings,
            errors=ctx.errors,
            where=ctx.where or "always_comb",
        )
        for name in latch_risks(self.body):
            inner.warnings.append((
                "latch",
                f"always_comb: '{name}' is not assigned on every path -- "
                f"this infers a latch; assign a default first or add else/default",
            ))
        lines = _comment_lines(self.comment, ctx)
        # A single-statement always_comb reads better without begin/end.
        if len(self.body) == 1:
            chunk = self.body[0].emit(inner.nested())
            if len(chunk) == 1:
                return [*lines, f"{ctx.pad()}always_comb {chunk[0].strip()}"]
        lines.append(f"{ctx.pad()}always_comb begin")
        for stmt in self.body:
            lines.extend(stmt.emit(inner.nested()))
        lines.append(f"{ctx.pad()}end")
        return lines


@dataclass
class AlwaysFF(Proc):
    """``always_ff`` -- a clocked block, non-blocking assignment."""

    clock: Expr
    body: tuple[Stmt, ...]
    reset: ResetSpec | None = None
    reset_body: tuple[Stmt, ...] = ()
    comment: str = ""
    posedge: bool = True

    def __init__(
        self,
        clock: Expr,
        *body,
        reset: ResetSpec | None = None,
        reset_body: Sequence[Stmt] | None = None,
        comment: str = "",
        posedge: bool = True,
    ):
        self.clock = lift(clock)
        self.body = _as_stmts(body)
        self.reset = reset
        self.reset_body = _as_stmts([reset_body]) if reset_body else ()
        self.comment = comment
        self.posedge = posedge
        if not self.body and not self.reset_body:
            raise SvError("always_ff block is empty")
        if self.reset_body and (self.reset is None or self.reset.signal is None):
            raise SvError("reset_body given but no reset signal")

    def body_stmts(self) -> tuple[Stmt, ...]:
        return self.reset_body + self.body

    def targets(self) -> list[str]:
        return [t for s in self.body_stmts() for t in s.targets()]

    def _inner_ctx(self, ctx: EmitCtx) -> EmitCtx:
        return EmitCtx(
            indent=ctx.indent,
            op="<=",
            tab=ctx.tab,
            env=ctx.env,
            warnings=ctx.warnings,
            errors=ctx.errors,
            where=ctx.where or "always_ff",
        )

    def _reset_if(self) -> Stmt:
        """The ``if (reset) ... else ...`` that a reset block wraps around."""
        assert self.reset is not None
        return If(self.reset.condition(), *self.reset_body).Else(*self.body)

    def emit(self, ctx: EmitCtx) -> list[str]:
        inner = self._inner_ctx(ctx)
        lines = _comment_lines(self.comment, ctx)
        edge = "posedge" if self.posedge else "negedge"
        clk = self.clock.render()

        if not self.reset_body:
            # No reset -- e.g. an inferred memory write port.
            return [*lines, *_wrap(f"always_ff @({edge} {clk})", self.body, inner, ctx)]

        spec = self.reset
        assert spec is not None and spec.signal is not None
        rst = spec.signal.render()

        if spec.style == "macro":
            # The macro takes a single statement; the if/else is exactly that.
            lines.append(f"{ctx.pad()}`{spec.macro}({clk}, {rst},")
            lines.extend(self._reset_if().emit(inner.nested()))
            lines.append(f"{ctx.pad()})")
            return lines

        if spec.style.startswith("async"):
            rst_edge = "negedge" if spec.active_low else "posedge"
            header = f"always_ff @({edge} {clk} or {rst_edge} {rst})"
        else:
            header = f"always_ff @({edge} {clk})"
        return [*lines, *_wrap(header, [self._reset_if()], inner, ctx)]


@dataclass
class AlwaysLatch(Proc):
    """``always_latch`` -- present for completeness; rarely what you want."""

    body: tuple[Stmt, ...]
    comment: str = ""

    def __init__(self, *body, comment: str = ""):
        self.body = _as_stmts(body)
        self.comment = comment

    def body_stmts(self) -> tuple[Stmt, ...]:
        return self.body

    def targets(self) -> list[str]:
        return [t for s in self.body for t in s.targets()]

    def emit(self, ctx: EmitCtx) -> list[str]:
        inner = EmitCtx(
            indent=ctx.indent, op="<=", tab=ctx.tab, env=ctx.env,
            warnings=ctx.warnings, errors=ctx.errors, where="always_latch",
        )
        lines = _comment_lines(self.comment, ctx)
        return [*lines, *_wrap("always_latch", self.body, inner, ctx)]


@dataclass
class ContinuousAssign(Stmt):
    """``assign lhs = rhs;`` at module scope."""

    target: Expr
    value: Expr
    comment: str = ""

    def __init__(self, target: Expr, value, comment: str = ""):
        self.target = target
        self.value = lift(value)
        self.comment = comment

    def targets(self) -> list[str]:
        from .stmt import _target_names

        return _target_names(self.target)

    def emit(self, ctx: EmitCtx) -> list[str]:
        from .expr import check_assign_width, expr_warnings

        problem = check_assign_width(self.target, self.value, ctx.env, "assign")
        if problem:
            ctx.warnings.append(("width", problem))
        for message in expr_warnings(self.value, ctx.env, "assign"):
            ctx.warnings.append(("logical-width", message))
        text = f"{ctx.pad()}assign {self.target.render()} = {self.value.render()};"
        if self.comment:
            text = f"{text}  // {self.comment}"
        return text.splitlines()


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------
def _comment_lines(comment: str, ctx: EmitCtx) -> list[str]:
    if not comment:
        return []
    return [f"{ctx.pad()}// {line}" for line in comment.splitlines()]


def _wrap(header: str, body: Sequence[Stmt], inner: EmitCtx, ctx: EmitCtx) -> list[str]:
    """``header begin ... end``, or bare when the body is a single line."""
    if len(body) == 1:
        chunk = body[0].emit(inner.nested())
        if len(chunk) == 1:
            return [f"{ctx.pad()}{header}", *chunk]
        # An if/else body needs no extra begin/end -- it is one statement.
        if isinstance(body[0], (If, Case)):
            return [f"{ctx.pad()}{header} begin", *chunk, f"{ctx.pad()}end"]
    lines = [f"{ctx.pad()}{header} begin"]
    for stmt in body:
        lines.extend(stmt.emit(inner.nested()))
    lines.append(f"{ctx.pad()}end")
    return lines


def latch_risks(body: Sequence[Stmt]) -> list[str]:
    """Names assigned conditionally but never unconditionally in *body*.

    In ``always_comb`` such a signal holds its previous value on some path,
    which synthesises to a latch. The usual fixes are a default assignment at
    the top of the block or a complete ``else``/``default``.
    """
    defaulted: set[str] = set()
    conditional: set[str] = set()

    def walk(stmts: Sequence[Stmt], guarded: bool) -> None:
        for stmt in stmts:
            if isinstance(stmt, If):
                complete = stmt.is_complete()
                for _, arm_body in stmt._arms:
                    walk(arm_body, guarded or not complete)
                if stmt._else:
                    walk(stmt._else, guarded or not complete)
                if not complete:
                    conditional.update(stmt.targets())
            elif isinstance(stmt, Case):
                complete = stmt.is_complete()
                for arm in stmt.arms:
                    walk(arm.body, guarded or not complete)
                if stmt.default:
                    walk(stmt.default, guarded or not complete)
                if not complete:
                    conditional.update(stmt.targets())
            elif hasattr(stmt, "body") and not isinstance(stmt, Proc):
                walk(getattr(stmt, "body"), guarded)
            elif guarded:
                conditional.update(stmt.targets())
            else:
                defaulted.update(stmt.targets())

    walk(body, False)
    return sorted(conditional - defaulted)
