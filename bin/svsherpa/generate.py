# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.generate
# Purpose: Elaboration-time generate constructs
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Generate blocks.

There are two distinct ways to repeat hardware from Python, and choosing the
right one matters:

**Python loop** -- unrolls at generation time. The emitted SV contains N
explicit statements. Use it when the count is fixed for this build, or when
each instance genuinely differs (a Dadda tree, a CRC XOR network).

**GenFor** -- emits an SV ``for (genvar i = ...)``. The count stays a
parameter, so one file serves every configuration. Use it when the RTL should
remain parameterizable at elaboration.

The genvar is handed to the body as an expression, so it can be indexed with
directly::

    GenFor("i", NUM_LANES, label="g_lane", body=lambda i: [
        Instance("SyncFIFO_Hsk", "u_fifo",
                 ports={"wr_data": wr_data[i], "rd_data": rd_data[i]}),
    ])
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

from .errors import SvError, check_identifier
from .expr import Expr, ExprLike, Raw, lift, width_of
from .stmt import EmitCtx, Stmt, _as_stmts
from .symint import SymInt


@dataclass(frozen=True, eq=False)
class GenVar(Expr):
    """A generate-loop index. Usable as an expression and as a width."""

    name: str

    @property
    def width(self) -> SymInt:
        return SymInt.lit(32)

    @property
    def sym_name(self) -> str:
        # Lets `q[i]` and `WIDTH*i` resolve through the width algebra.
        return self.name

    def render(self, prec: int = 0) -> str:
        return self.name


class GenFor(Stmt):
    """``for (genvar i = 0; i < COUNT; i++) begin : label ... end``"""

    def __init__(
        self,
        var: str,
        count: ExprLike,
        *,
        label: str,
        body: Sequence[Stmt] | Callable[[GenVar], Sequence[Stmt]],
        start: ExprLike = 0,
        wrap: bool = False,
    ):
        check_identifier(var, "genvar")
        check_identifier(label, "generate label")
        self.var = GenVar(var)
        self.count = lift(count)
        self.start = lift(start)
        self.label = label
        self.wrap = wrap
        resolved = body(self.var) if callable(body) else body
        self.body = _as_stmts([resolved])
        if not self.body:
            raise SvError(f"generate block {label!r} is empty")

    def targets(self) -> list[str]:
        return [t for s in self.body for t in s.targets()]

    def emit(self, ctx: EmitCtx) -> list[str]:
        pad = ctx.pad()
        name = self.var.name
        header = (
            f"for (genvar {name} = {self.start.render()}; "
            f"{name} < {self.count.render()}; {name}++) begin : {self.label}"
        )
        inner = ctx.nested() if not self.wrap else ctx.nested(2)
        lines = [f"{pad}generate"] if self.wrap else []
        body_pad = ctx.pad(1) if self.wrap else pad
        lines.append(f"{body_pad}{header}")
        for stmt in self.body:
            lines.extend(stmt.emit(inner))
        lines.append(f"{body_pad}end")
        if self.wrap:
            lines.append(f"{pad}endgenerate")
        return lines


class GenIf(Stmt):
    """``if (COND) begin : label ... end else begin : label ... end``

    The condition must be elaboration-time constant -- a parameter or an
    expression over parameters. Both branches usually share a port signature,
    which is what makes this useful for pipeline-stage templates.
    """

    def __init__(
        self,
        cond: ExprLike,
        *,
        label: str,
        body: Sequence[Stmt],
        else_label: str = "",
        else_body: Sequence[Stmt] | None = None,
        wrap: bool = False,
    ):
        check_identifier(label, "generate label")
        if else_body and not else_label:
            raise SvError("an else branch needs its own label")
        if else_label:
            check_identifier(else_label, "generate label")
        self.cond = lift(cond)
        self.label = label
        self.body = _as_stmts([body])
        self.else_label = else_label
        self.else_body = _as_stmts([else_body]) if else_body else ()
        self.wrap = wrap

    def targets(self) -> list[str]:
        return [t for s in (*self.body, *self.else_body) for t in s.targets()]

    def emit(self, ctx: EmitCtx) -> list[str]:
        pad = ctx.pad()
        lines = [f"{pad}generate"] if self.wrap else []
        body_pad = ctx.pad(1) if self.wrap else pad
        inner = ctx.nested(2) if self.wrap else ctx.nested()

        lines.append(f"{body_pad}if ({self.cond.render()}) begin : {self.label}")
        for stmt in self.body:
            lines.extend(stmt.emit(inner))
        if self.else_body:
            lines.append(f"{body_pad}end else begin : {self.else_label}")
            for stmt in self.else_body:
                lines.extend(stmt.emit(inner))
        lines.append(f"{body_pad}end")
        if self.wrap:
            lines.append(f"{pad}endgenerate")
        return lines


def genvar_expr(name: str) -> GenVar:
    """A bare genvar reference, for hand-written generate scopes."""
    return GenVar(name)


def raw_expr(text: str, width=1) -> Expr:
    """Literal SV text as an expression, with a declared width."""
    return Raw(text, width_of(width))
