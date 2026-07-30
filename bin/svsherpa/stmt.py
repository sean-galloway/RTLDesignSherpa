# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.stmt
# Purpose: Procedural statements -- assignment, if, case, blocks
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Procedural statements.

Statements are immutable trees built by nesting, which keeps the Python shaped
like the SV it produces::

    If(enable,
        If(count == max_val,
            count.set(ZERO),
        ).Else(
            count.set(count + 1),
        ),
    ).Else(
        count.set(count),
    )

``begin``/``end`` is emitted only when a branch holds more than one statement,
matching hand-written house style rather than bracketing everything.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Iterable, Sequence

from .errors import SvError
from .expr import Expr, ExprLike, lift

TAB = "    "


@dataclass
class EmitCtx:
    """Mutable emission context threaded through a statement tree."""

    indent: int = 1
    op: str = "="                       # "=" inside always_comb, "<=" in always_ff
    tab: str = TAB
    env: dict = field(default_factory=dict)     # param name -> int, for checks
    warnings: list = field(default_factory=list)
    errors: list = field(default_factory=list)
    where: str = ""

    def pad(self, extra: int = 0) -> str:
        return self.tab * (self.indent + extra)

    def nested(self, extra: int = 1) -> "EmitCtx":
        return replace(self, indent=self.indent + extra)


class Stmt:
    """Base class for procedural statements."""

    def emit(self, ctx: EmitCtx) -> list[str]:  # pragma: no cover - abstract
        raise NotImplementedError

    def targets(self) -> list[str]:
        """Names this statement drives, for driver and latch analysis."""
        return []

    def __str__(self) -> str:
        return "\n".join(self.emit(EmitCtx(indent=0)))


def _as_stmts(items) -> tuple[Stmt, ...]:
    """Flatten a mix of statements, lists and None into a statement tuple."""
    out: list[Stmt] = []
    for item in items:
        if item is None:
            continue
        if isinstance(item, Stmt):
            out.append(item)
        elif isinstance(item, (list, tuple)):
            out.extend(_as_stmts(item))
        else:
            raise SvError(
                f"expected a statement, got {item!r} of type {type(item).__name__}"
            )
    return tuple(out)


def _emit_branch(header: str, body: Sequence[Stmt], ctx: EmitCtx) -> list[str]:
    """Emit ``header`` followed by ``body``, bracketing only when necessary.

    A single-line body renders bare beneath the header, the way hand-written
    house style does it::

        if (!rst_n)
            count <= '0;

    Anything longer gets ``begin``/``end``. An empty body renders ``header ;``
    so a deliberately empty case arm stays legal.
    """
    pad = ctx.pad()
    if not body:
        return [f"{pad}{header} ;"]
    if len(body) == 1:
        inner = body[0].emit(ctx.nested())
        if len(inner) == 1:
            return [f"{pad}{header}", *inner]
    lines = [f"{pad}{header} begin"]
    for stmt in body:
        lines.extend(stmt.emit(ctx.nested()))
    lines.append(f"{pad}end")
    return lines


def _chain(prev: list[str], chunk: list[str], ctx: EmitCtx) -> list[str]:
    """Join an ``else``/``else if`` chunk onto the preceding branch.

    When the previous branch closed with ``end`` the two merge into
    ``end else ...``; otherwise the ``else`` simply follows on its own line.
    """
    pad = ctx.pad()
    if prev and prev[-1] == f"{pad}end":
        return [*prev[:-1], f"{pad}end {chunk[0][len(pad):]}", *chunk[1:]]
    return [*prev, *chunk]


@dataclass
class Assignment(Stmt):
    """An assignment whose operator is supplied by the enclosing process."""

    target: Expr
    value: Expr

    def __init__(self, target: Expr, value: ExprLike):
        self.target = target
        self.value = lift(value)

    def targets(self) -> list[str]:
        return _target_names(self.target)

    def emit(self, ctx: EmitCtx) -> list[str]:
        from .expr import check_assign_width, expr_warnings

        problem = check_assign_width(self.target, self.value, ctx.env, ctx.where)
        if problem:
            ctx.warnings.append(("width", problem))
        for message in expr_warnings(self.value, ctx.env, ctx.where):
            ctx.warnings.append(("logical-width", message))
        return [f"{ctx.pad()}{self.target.render()} {ctx.op} {self.value.render()};"]


@dataclass
class Block(Stmt):
    """An explicit ``begin``/``end`` block, optionally labelled."""

    body: tuple[Stmt, ...]
    label: str = ""

    def __init__(self, *body, label: str = ""):
        self.body = _as_stmts(body)
        self.label = label

    def targets(self) -> list[str]:
        return [t for s in self.body for t in s.targets()]

    def emit(self, ctx: EmitCtx) -> list[str]:
        tag = f" : {self.label}" if self.label else ""
        lines = [f"{ctx.pad()}begin{tag}"]
        for stmt in self.body:
            lines.extend(stmt.emit(ctx.nested()))
        lines.append(f"{ctx.pad()}end")
        return lines


@dataclass
class Comment(Stmt):
    """A ``//`` comment carried into the output."""

    text: str

    def emit(self, ctx: EmitCtx) -> list[str]:
        return [f"{ctx.pad()}// {line}" for line in self.text.splitlines() or [""]]


@dataclass
class Raw(Stmt):
    """Literal SV lines, re-indented. The escape hatch for anything missing."""

    text: str

    def emit(self, ctx: EmitCtx) -> list[str]:
        return [
            f"{ctx.pad()}{line.strip()}" if line.strip() else ""
            for line in self.text.splitlines()
        ]


class If(Stmt):
    """``if`` / ``else if`` / ``else``.

    Chained with ``.Elif(...)`` and ``.Else(...)``, which return new objects
    rather than mutating, so a partially built conditional is safe to reuse.
    """

    def __init__(self, cond: ExprLike, *body):
        self._arms: tuple[tuple[Expr, tuple[Stmt, ...]], ...] = (
            (lift(cond), _as_stmts(body)),
        )
        self._else: tuple[Stmt, ...] | None = None

    def _clone(self, arms, else_body) -> "If":
        new = If.__new__(If)
        new._arms = arms
        new._else = else_body
        return new

    def Elif(self, cond: ExprLike, *body) -> "If":
        if self._else is not None:
            raise SvError("Elif cannot follow Else")
        return self._clone(self._arms + ((lift(cond), _as_stmts(body)),), None)

    def Else(self, *body) -> "If":
        if self._else is not None:
            raise SvError("Else specified twice")
        return self._clone(self._arms, _as_stmts(body))

    def targets(self) -> list[str]:
        found = [t for _, body in self._arms for s in body for t in s.targets()]
        if self._else:
            found += [t for s in self._else for t in s.targets()]
        return found

    def is_complete(self) -> bool:
        """True when every path assigns -- i.e. there is an ``else``."""
        return self._else is not None

    def emit(self, ctx: EmitCtx) -> list[str]:
        first_cond, first_body = self._arms[0]
        lines = _emit_branch(f"if ({first_cond.render()})", first_body, ctx)
        for cond, body in self._arms[1:]:
            chunk = _emit_branch(f"else if ({cond.render()})", body, ctx)
            lines = _chain(lines, chunk, ctx)
        if self._else is not None:
            lines = _chain(lines, _emit_branch("else", self._else, ctx), ctx)
        return lines


@dataclass
class CaseArm:
    """One arm of a ``case``: one or more match values and a body."""

    matches: tuple[Expr, ...]
    body: tuple[Stmt, ...]

    def __init__(self, matches, *body):
        if not isinstance(matches, (list, tuple)):
            matches = [matches]
        self.matches = tuple(lift(m) for m in matches)
        self.body = _as_stmts(body)


class Case(Stmt):
    """``case`` / ``unique case`` / ``priority case`` / ``casez``.

    ``kind`` is written the way it appears in SV: ``"case"``, ``"unique case"``,
    ``"priority case"``, ``"casez"``, ``"unique casez"``.

    Arms are ``(match, *body)`` tuples; a match may be a list to fold several
    values onto one arm. ``default`` takes a body, and passing ``[]`` emits the
    empty ``default: ;`` that keeps a case statement latch-free.
    """

    def __init__(
        self,
        selector: ExprLike,
        *arms,
        default=None,
        kind: str = "case",
    ):
        self.selector = lift(selector)
        self.kind = kind
        self.arms: list[CaseArm] = []
        for arm in arms:
            if isinstance(arm, CaseArm):
                self.arms.append(arm)
            elif isinstance(arm, tuple) and arm:
                self.arms.append(CaseArm(arm[0], *arm[1:]))
            else:
                raise SvError(f"bad case arm {arm!r}; expected (match, *body)")
        self.default = None if default is None else _as_stmts([default])

    def targets(self) -> list[str]:
        found = [t for arm in self.arms for s in arm.body for t in s.targets()]
        if self.default:
            found += [t for s in self.default for t in s.targets()]
        return found

    def is_complete(self) -> bool:
        return self.default is not None

    def emit(self, ctx: EmitCtx) -> list[str]:
        pad = ctx.pad()
        lines = [f"{pad}{self.kind} ({self.selector.render()})"]
        inner = ctx.nested()
        labels = [", ".join(m.render() for m in arm.matches) for arm in self.arms]
        if self.default is not None:
            labels.append("default")
        pad_to = max((len(text) for text in labels), default=0)

        for arm, label in zip(self.arms, labels):
            lines.extend(_emit_arm(f"{label}:".ljust(pad_to + 1), arm.body, inner))
        if self.default is not None:
            lines.extend(
                _emit_arm(f"{'default':<{pad_to}}:", self.default, inner)
            )
        lines.append(f"{pad}endcase")
        return lines


def _emit_arm(label: str, body: Sequence[Stmt], ctx: EmitCtx) -> list[str]:
    """``label: stmt;`` on one line, or ``label: begin ... end``."""
    pad = ctx.pad()
    if not body:
        return [f"{pad}{label} ;"]
    if len(body) == 1:
        inner = body[0].emit(ctx)
        if len(inner) == 1:
            return [f"{pad}{label} {inner[0].strip()}"]
    lines = [f"{pad}{label} begin"]
    for stmt in body:
        lines.extend(stmt.emit(ctx.nested()))
    lines.append(f"{pad}end")
    return lines


def _root_name(node: Expr) -> str:
    """The underlying signal name of an assignment target."""
    current = node
    for _ in range(16):
        if hasattr(current, "name"):
            return getattr(current, "name")
        nxt = getattr(current, "operand", None)
        if nxt is None:
            break
        current = nxt
    return current.render()


def _target_names(node: Expr) -> list[str]:
    """Every signal driven by an assignment target.

    A concatenation target drives each of its parts, so ``{hi, lo} = bus``
    registers both -- otherwise the driver check would miss a second driver on
    ``hi``.
    """
    parts = getattr(node, "parts", None)
    if parts is not None:
        return [name for part in parts for name in _target_names(part)]
    return [_root_name(node)]


def assigned_names(body: Iterable[Stmt]) -> set[str]:
    """Every signal name driven anywhere in *body*."""
    return {name for stmt in body for name in stmt.targets()}
