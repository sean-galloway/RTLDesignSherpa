# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.expr
# Purpose: Width-aware SystemVerilog expression tree
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Expressions.

Every expression knows its own width, so mistakes that normally survive until
Verilator (or worse, until silicon) are caught where they are written::

    >>> a = Logic("a", 8)
    >>> b = Logic("b", 4)
    >>> str(a + b)
    'a + b'

Rendering is precedence-aware: parentheses appear only where SystemVerilog
needs them, so the output reads like something a person wrote. Note that this
makes ``~(a | b)`` come out correctly parenthesised -- writing ``~a | b`` would
be a different circuit, and ``~|`` would be a reduction NOR.

One deliberate Python wart: ``__eq__`` builds an SV ``==`` expression instead of
comparing objects, because ``a == b`` reading as ``a == b`` matters more here
than Python equality semantics. Expressions therefore hash by identity, and
structural comparison is done with :func:`same`.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from .errors import SvError
from .symint import SymInt, width_of as _sym_of

# ---------------------------------------------------------------------------
# SystemVerilog operator precedence. Larger binds tighter. Values follow the
# ordering in IEEE 1800 Table 11-2; only the relative order matters.
# ---------------------------------------------------------------------------
P_ATOM = 100
P_UNARY = 90
P_POW = 85
P_MUL = 80
P_ADD = 75
P_SHIFT = 70
P_REL = 65
P_EQ = 60
P_BAND = 55
P_BXOR = 50
P_BOR = 45
P_LAND = 40
P_LOR = 35
P_COND = 30

ExprLike = "Expr | int"


def width_of(value) -> SymInt:
    """Coerce *value* to a width, accepting ints, SymInts, or expressions.

    This is what lets a parameter be written the same way in both roles, as it
    is in SystemVerilog::

        m.logic("data", WIDTH)        # a width
        m.assign(full, count == MAX)  # an expression

    Expressions that are not simple parameter arithmetic degrade to an opaque
    atom: still rendered correctly, just not simplified or width-checked.
    """
    if isinstance(value, SymInt):
        return value
    if isinstance(value, Expr):
        return _expr_to_sym(value)
    return _sym_of(value)


def _expr_to_sym(node: "Expr") -> SymInt:
    """Best-effort translation of an expression into width algebra."""
    # Parameters and localparams expose `sym_name`; duck-typed to avoid a
    # circular import with the signals module.
    name = getattr(node, "sym_name", None)
    if name is not None:
        return SymInt.ref(name)
    if isinstance(node, Literal):
        return SymInt.lit(node.value)
    if isinstance(node, Binary):
        lhs, rhs = _expr_to_sym(node.lhs), _expr_to_sym(node.rhs)
        if node.op == "+":
            return lhs + rhs
        if node.op == "-":
            return lhs - rhs
        if node.op == "*":
            return lhs * rhs
    if isinstance(node, Unary) and node.op == "-":
        return -_expr_to_sym(node.operand)
    if isinstance(node, SysCall) and node.name == "$clog2" and node.args:
        return SymInt.clog2(_expr_to_sym(node.args[0]))
    return SymInt.opaque(node.render())


def _require_selectable(operand: "Expr") -> None:
    """Reject a select applied to an operator result.

    ``(a * b)[7:0]`` is not legal SystemVerilog -- a select needs a variable or
    another select, not a parenthesised expression. Catching it here beats
    emitting a file that will not parse.
    """
    if operand.is_lvalue():
        return
    raise SvError(
        f"cannot select bits of {operand.render()!r}: SystemVerilog only "
        f"allows a select on a variable. Assign it to an intermediate "
        f"signal first, then select from that."
    )


def lift(value: ExprLike) -> "Expr":
    """Coerce Python ints to unsized SV literals; pass Exprs through."""
    if isinstance(value, Expr):
        return value
    if isinstance(value, bool):
        return Literal(1 if value else 0, SymInt.lit(1))
    if isinstance(value, int):
        # Unsized: width is context-determined in SV. Track the minimum width
        # needed so obvious truncation is still catchable.
        return Literal(value, SymInt.lit(max(1, value.bit_length())), sized=False)
    raise SvError(f"cannot use {value!r} of type {type(value).__name__} in an expression")


@dataclass(frozen=True, eq=False)
class Expr:
    """Base class for every SystemVerilog expression node."""

    # Subclasses set these via dataclass fields.
    def render(self, prec: int = 0) -> str:  # pragma: no cover - abstract
        raise NotImplementedError

    @property
    def width(self) -> SymInt:  # pragma: no cover - abstract
        raise NotImplementedError

    @property
    def signed(self) -> bool:
        return False

    # ---------------------------------------------------------------- lvalues
    def is_lvalue(self) -> bool:
        """Whether this expression can appear on the left of an assignment.

        Signals, selects, field references and concatenations of those are
        assignable; the result of an operator is not.
        """
        return False

    def set(self, value: ExprLike):
        """Assign *value* to this expression.

        The operator (``=``, ``<=``, ``assign``) comes from the enclosing
        process, never from here.
        """
        if not self.is_lvalue():
            raise SvError(
                f"cannot assign to {self.render()!r}: not an lvalue. "
                f"Assign it to an intermediate signal first."
            )
        from .stmt import Assignment

        return Assignment(self, value)

    # -------------------------------------------------------------- rendering
    def __str__(self) -> str:
        return self.render()

    def __repr__(self) -> str:
        return f"<{type(self).__name__} {self.render()}>"

    __hash__ = object.__hash__

    # ------------------------------------------------------- arithmetic ops
    def __add__(self, other: ExprLike) -> "Expr":
        return Binary("+", self, lift(other), P_ADD)

    def __radd__(self, other: ExprLike) -> "Expr":
        return Binary("+", lift(other), self, P_ADD)

    def __sub__(self, other: ExprLike) -> "Expr":
        return Binary("-", self, lift(other), P_ADD)

    def __rsub__(self, other: ExprLike) -> "Expr":
        return Binary("-", lift(other), self, P_ADD)

    def __mul__(self, other: ExprLike) -> "Expr":
        return Binary("*", self, lift(other), P_MUL, width_rule="sum")

    def __rmul__(self, other: ExprLike) -> "Expr":
        return Binary("*", lift(other), self, P_MUL, width_rule="sum")

    def __floordiv__(self, other: ExprLike) -> "Expr":
        return Binary("/", self, lift(other), P_MUL)

    def __truediv__(self, other: ExprLike) -> "Expr":
        # SV has no distinct integer/real division for logic vectors.
        return Binary("/", self, lift(other), P_MUL)

    def __mod__(self, other: ExprLike) -> "Expr":
        return Binary("%", self, lift(other), P_MUL)

    def __pow__(self, other: ExprLike) -> "Expr":
        return Binary("**", self, lift(other), P_POW)

    # ---------------------------------------------------------- bitwise ops
    def __and__(self, other: ExprLike) -> "Expr":
        return Binary("&", self, lift(other), P_BAND)

    def __rand__(self, other: ExprLike) -> "Expr":
        return Binary("&", lift(other), self, P_BAND)

    def __or__(self, other: ExprLike) -> "Expr":
        return Binary("|", self, lift(other), P_BOR)

    def __ror__(self, other: ExprLike) -> "Expr":
        return Binary("|", lift(other), self, P_BOR)

    def __xor__(self, other: ExprLike) -> "Expr":
        return Binary("^", self, lift(other), P_BXOR)

    def __rxor__(self, other: ExprLike) -> "Expr":
        return Binary("^", lift(other), self, P_BXOR)

    def __invert__(self) -> "Expr":
        return Unary("~", self)

    def __lshift__(self, other: ExprLike) -> "Expr":
        return Binary("<<", self, lift(other), P_SHIFT, width_rule="left")

    def __rshift__(self, other: ExprLike) -> "Expr":
        return Binary(">>", self, lift(other), P_SHIFT, width_rule="left")

    def __neg__(self) -> "Expr":
        return Unary("-", self)

    def __pos__(self) -> "Expr":
        return self

    # ------------------------------------------------------- comparison ops
    def __lt__(self, other: ExprLike) -> "Expr":
        return Binary("<", self, lift(other), P_REL, width_rule="bool")

    def __gt__(self, other: ExprLike) -> "Expr":
        return Binary(">", self, lift(other), P_REL, width_rule="bool")

    def __le__(self, other: ExprLike) -> "Expr":
        return Binary("<=", self, lift(other), P_REL, width_rule="bool")

    def __ge__(self, other: ExprLike) -> "Expr":
        return Binary(">=", self, lift(other), P_REL, width_rule="bool")

    def __eq__(self, other: ExprLike) -> "Expr":  # type: ignore[override]
        return Binary("==", self, lift(other), P_EQ, width_rule="bool")

    def __ne__(self, other: ExprLike) -> "Expr":  # type: ignore[override]
        return Binary("!=", self, lift(other), P_EQ, width_rule="bool")

    # SystemVerilog's 4-state comparisons have no Python operator.
    def eqx(self, other: ExprLike) -> "Expr":
        """``===`` -- case equality, x and z compared literally."""
        return Binary("===", self, lift(other), P_EQ, width_rule="bool")

    def nex(self, other: ExprLike) -> "Expr":
        """``!==`` -- case inequality."""
        return Binary("!==", self, lift(other), P_EQ, width_rule="bool")

    # ------------------------------------------------------- logical ops
    # Python cannot overload `and`/`or`/`not`, so these are spelled out.
    def land(self, *others: ExprLike) -> "Expr":
        """``&&``"""
        node = self
        for other in others:
            node = Binary("&&", node, lift(other), P_LAND, width_rule="bool")
        return node

    def lor(self, *others: ExprLike) -> "Expr":
        """``||``"""
        node = self
        for other in others:
            node = Binary("||", node, lift(other), P_LOR, width_rule="bool")
        return node

    def lnot(self) -> "Expr":
        """``!``"""
        return Unary("!", self, width_rule="bool")

    # ------------------------------------------------------- reduction ops
    def ror(self) -> "Expr":
        """``|x`` -- OR reduction: any bit set."""
        return Unary("|", self, width_rule="bool")

    def rand(self) -> "Expr":
        """``&x`` -- AND reduction: all bits set."""
        return Unary("&", self, width_rule="bool")

    def rxor(self) -> "Expr":
        """``^x`` -- XOR reduction: parity."""
        return Unary("^", self, width_rule="bool")

    def rnor(self) -> "Expr":
        """``~|x`` -- NOR reduction: no bit set."""
        return Unary("~|", self, width_rule="bool")

    def rnand(self) -> "Expr":
        """``~&x`` -- NAND reduction."""
        return Unary("~&", self, width_rule="bool")

    def rxnor(self) -> "Expr":
        """``~^x`` -- XNOR reduction: even parity."""
        return Unary("~^", self, width_rule="bool")

    # ------------------------------------------------------------ selection
    def __getitem__(self, key) -> "Expr":
        """Bit select ``x[i]`` or part select ``x[msb:lsb]``.

        Python slice order is kept as written, so ``x[7:0]`` in Python emits
        ``x[7:0]`` -- descending, the way SV part selects are written. This is
        the opposite of Python list semantics, and it is intentional: the code
        should read like the SV it becomes.
        """
        if isinstance(key, slice):
            if key.step is not None:
                raise SvError("part select does not take a step")
            return PartSelect(self, width_of(key.start), width_of(key.stop))
        return BitSelect(self, width_of(key))

    def bit(self, index) -> "Expr":
        """Explicit single-bit select, for when ``[]`` reads ambiguously."""
        return BitSelect(self, width_of(index))

    # -------------------------------------------------------------- casting
    def cast(self, width) -> "Expr":
        """``WIDTH'(expr)`` -- a sized cast, the safe way to change width."""
        return Cast(self, width_of(width))

    def signed_(self) -> "Expr":
        """``$signed(expr)``"""
        return SysCall("$signed", (self,), self.width)

    def unsigned_(self) -> "Expr":
        """``$unsigned(expr)``"""
        return SysCall("$unsigned", (self,), self.width)


# ---------------------------------------------------------------------------
# Leaf nodes
# ---------------------------------------------------------------------------
@dataclass(frozen=True, eq=False)
class Literal(Expr):
    """A numeric literal, sized (``8'hFF``) or unsized (``42``)."""

    value: int
    _width: SymInt
    sized: bool = True
    base: str = "h"

    @property
    def width(self) -> SymInt:
        return self._width

    def render(self, prec: int = 0) -> str:
        if not self.sized:
            return str(self.value)
        wide = self._width.render()
        if self.base == "b":
            bits = self._width.try_eval({})
            body = format(self.value, f"0{bits}b") if bits else format(self.value, "b")
            return f"{wide}'b{body}"
        if self.base == "d":
            return f"{wide}'d{self.value}"
        return f"{wide}'h{self.value:x}"


@dataclass(frozen=True, eq=False)
class Fill(Expr):
    """``'0`` / ``'1`` -- width-agnostic fill, sized by its assignment context.

    Preferred over ``{N{1'b0}}`` because it never needs updating when a width
    changes, which is exactly the kind of edit that rots by hand.
    """

    bit: int
    _width: SymInt | None = None

    @property
    def width(self) -> SymInt:
        # A fill adopts its context width; report 0 so width checks skip it.
        return self._width if self._width is not None else SymInt.lit(0)

    def render(self, prec: int = 0) -> str:
        return f"'{self.bit}"


@dataclass(frozen=True, eq=False)
class Raw(Expr):
    """An escape hatch: literal SV text with a declared width.

    Present because no generator covers every construct, and being stuck is
    worse than being impure. Nothing inside is checked.
    """

    text: str
    _width: SymInt = SymInt()

    @property
    def width(self) -> SymInt:
        return self._width

    def render(self, prec: int = 0) -> str:
        return self.text


# ---------------------------------------------------------------------------
# Operators
# ---------------------------------------------------------------------------
def _resolve_binary_width(op: str, lhs: Expr, rhs: Expr, rule: str) -> SymInt:
    """Width of a binary result, per SV context-determined operand rules."""
    if rule == "bool":
        return SymInt.lit(1)
    if rule == "left":
        return lhs.width
    lw, rw = lhs.width, rhs.width
    if rule == "sum":  # multiply: full precision
        return lw + rw
    # Arithmetic/bitwise: max of operands. Unsized literals defer to the other
    # side rather than dragging the result down to their minimum width.
    if isinstance(lhs, (Literal, Fill)) and not getattr(lhs, "sized", True):
        return rw
    if isinstance(rhs, (Literal, Fill)) and not getattr(rhs, "sized", True):
        return lw
    if isinstance(lhs, Fill):
        return rw
    if isinstance(rhs, Fill):
        return lw
    left, right = lw.try_eval({}), rw.try_eval({})
    if left is not None and right is not None:
        return lw if left >= right else rw
    return lw


@dataclass(frozen=True, eq=False)
class Binary(Expr):
    """A binary operation such as ``a + b`` or ``a & b``."""

    op: str
    lhs: Expr
    rhs: Expr
    prec: int
    width_rule: str = "max"

    @property
    def width(self) -> SymInt:
        return _resolve_binary_width(self.op, self.lhs, self.rhs, self.width_rule)

    @property
    def signed(self) -> bool:
        return self.lhs.signed and self.rhs.signed

    def render(self, prec: int = 0) -> str:
        # Under `&&`/`||`, parenthesise comparison operands even though
        # precedence does not require it: `(a == b) || (c != d)` is how this
        # gets written by hand, and the parens are what make it scannable.
        if self.op in ("&&", "||"):
            left = self.lhs.render(P_REL + 1)
            right = self.rhs.render(P_REL + 1)
        else:
            # Right operand gets prec+1 so `a - (b - c)` keeps its parentheses.
            left = self.lhs.render(self.prec)
            right = self.rhs.render(self.prec + 1)
        text = f"{left} {self.op} {right}"
        return f"({text})" if prec > self.prec else text


@dataclass(frozen=True, eq=False)
class Unary(Expr):
    """A unary or reduction operation such as ``~a`` or ``|a``."""

    op: str
    operand: Expr
    width_rule: str = "same"

    @property
    def width(self) -> SymInt:
        return SymInt.lit(1) if self.width_rule == "bool" else self.operand.width

    def render(self, prec: int = 0) -> str:
        text = f"{self.op}{self.operand.render(P_UNARY)}"
        return f"({text})" if prec > P_UNARY else text


@dataclass(frozen=True, eq=False)
class Cast(Expr):
    """``WIDTH'(expr)`` -- an explicit sized cast."""

    operand: Expr
    _width: SymInt

    @property
    def width(self) -> SymInt:
        return self._width

    def render(self, prec: int = 0) -> str:
        return f"{self._width.render(P_UNARY)}'({self.operand.render()})"


@dataclass(frozen=True, eq=False)
class BitSelect(Expr):
    """``x[i]``"""

    operand: Expr
    index: SymInt

    def __post_init__(self) -> None:
        _require_selectable(self.operand)

    def is_lvalue(self) -> bool:
        return self.operand.is_lvalue()

    @property
    def width(self) -> SymInt:
        return SymInt.lit(1)

    def render(self, prec: int = 0) -> str:
        return f"{self.operand.render(P_ATOM)}[{self.index.render()}]"


@dataclass(frozen=True, eq=False)
class PartSelect(Expr):
    """``x[msb:lsb]``"""

    operand: Expr
    msb: SymInt
    lsb: SymInt

    def __post_init__(self) -> None:
        _require_selectable(self.operand)

    def is_lvalue(self) -> bool:
        return self.operand.is_lvalue()

    @property
    def width(self) -> SymInt:
        return self.msb - self.lsb + 1

    def render(self, prec: int = 0) -> str:
        return (
            f"{self.operand.render(P_ATOM)}"
            f"[{self.msb.render()}:{self.lsb.render()}]"
        )


@dataclass(frozen=True, eq=False)
class Concat(Expr):
    """``{a, b, c}``"""

    parts: tuple[Expr, ...]

    def __init__(self, *parts: ExprLike):
        if not parts:
            raise SvError("Concat needs at least one operand")
        object.__setattr__(self, "parts", tuple(lift(p) for p in parts))

    def is_lvalue(self) -> bool:
        return all(part.is_lvalue() for part in self.parts)

    @property
    def width(self) -> SymInt:
        total = SymInt.lit(0)
        for part in self.parts:
            total = total + part.width
        return total

    def render(self, prec: int = 0) -> str:
        inner = ", ".join(p.render() for p in self.parts)
        return f"{{{inner}}}"


@dataclass(frozen=True, eq=False)
class Repl(Expr):
    """``{N{expr}}`` -- replication."""

    count: SymInt
    operand: Expr

    def __init__(self, count, operand: ExprLike):
        object.__setattr__(self, "count", width_of(count))
        object.__setattr__(self, "operand", lift(operand))

    @property
    def width(self) -> SymInt:
        return self.count * self.operand.width

    def render(self, prec: int = 0) -> str:
        # A compound replication count must be parenthesised: `{WIDTH-1{1'b0}}`
        # is a parse hazard, `{(WIDTH-1){1'b0}}` is unambiguous.
        count = self.count.render()
        if not count.isidentifier() and not count.isdigit():
            count = f"({count})"
        return f"{{{count}{{{self.operand.render()}}}}}"


@dataclass(frozen=True, eq=False)
class Cond(Expr):
    """``sel ? a : b`` -- the ternary conditional."""

    sel: Expr
    then: Expr
    other: Expr

    def __init__(self, sel: ExprLike, then: ExprLike, other: ExprLike):
        object.__setattr__(self, "sel", lift(sel))
        object.__setattr__(self, "then", lift(then))
        object.__setattr__(self, "other", lift(other))

    @property
    def width(self) -> SymInt:
        return _resolve_binary_width("?:", self.then, self.other, "max")

    def render(self, prec: int = 0) -> str:
        text = (
            f"{self.sel.render(P_COND + 1)} ? "
            f"{self.then.render(P_COND + 1)} : {self.other.render(P_COND)}"
        )
        return f"({text})" if prec > P_COND else text


@dataclass(frozen=True, eq=False)
class SysCall(Expr):
    """A system function call such as ``$clog2(x)`` or ``$signed(x)``."""

    name: str
    args: tuple[Expr, ...]
    _width: SymInt

    @property
    def width(self) -> SymInt:
        return self._width

    def render(self, prec: int = 0) -> str:
        inner = ", ".join(a.render() for a in self.args)
        return f"{self.name}({inner})" if inner else f"{self.name}"


@dataclass(frozen=True, eq=False)
class FuncCall(Expr):
    """A call to a user-defined SV function."""

    name: str
    args: tuple[Expr, ...]
    _width: SymInt

    def __init__(self, name: str, args: Sequence[ExprLike], width):
        object.__setattr__(self, "name", name)
        object.__setattr__(self, "args", tuple(lift(a) for a in args))
        object.__setattr__(self, "_width", width_of(width))

    @property
    def width(self) -> SymInt:
        return self._width

    def render(self, prec: int = 0) -> str:
        inner = ", ".join(a.render() for a in self.args)
        return f"{self.name}({inner})"


# ---------------------------------------------------------------------------
# Free functions -- these are the names an SV coder reaches for
# ---------------------------------------------------------------------------
def C(value: int, width=None, base: str = "h") -> Expr:
    """A constant. ``C(0)`` is unsized; ``C(5, 8)`` is ``8'h5``.

    ``base`` selects the radix used when rendering: ``h``, ``b`` or ``d``.
    """
    if width is None:
        return lift(value)
    return Literal(value, width_of(width), sized=True, base=base)


def B(value: int, width) -> Expr:
    """A binary-rendered constant, e.g. ``B(0b10, 2)`` -> ``2'b10``."""
    return Literal(value, width_of(width), sized=True, base="b")


ZERO = Fill(0)
ONES = Fill(1)


def mux(sel: ExprLike, then: ExprLike, other: ExprLike) -> Expr:
    """``sel ? then : other``"""
    return Cond(sel, then, other)


def clog2(value) -> SymInt:
    """``$clog2(value)`` as a width, accepting a parameter or an expression.

    Folded to a constant when the argument is known, so ``clog2(8)`` is ``3``
    rather than a call left in the output.
    """
    return SymInt.clog2(width_of(value))


def clog2_expr(value: ExprLike) -> Expr:
    """``$clog2(value)`` as an expression (see ``symint.clog2`` for widths)."""
    return SysCall("$clog2", (lift(value),), SymInt.lit(32))


def same(lhs: Expr, rhs: Expr) -> bool:
    """Structural comparison, since ``==`` builds an SV expression instead."""
    return lhs.render() == rhs.render()


def expr_warnings(node: Expr, env, where: str) -> list[str]:
    """Diagnostics found by walking an expression tree.

    Currently one rule, and it earns its place: a logical operator applied to a
    multi-bit operand. ``a && b`` on two 8-bit vectors silently means
    ``(a != 0) && (b != 0)``, which is virtually never the intent -- the intent
    is a reduction (``a.ror()``) or an explicit comparison. Verilator flags this
    as WIDTHTRUNC; catching it here names the operand.
    """
    found: list[str] = []

    def walk(current: Expr) -> None:
        if isinstance(current, Binary):
            if current.op in ("&&", "||"):
                for side in (current.lhs, current.rhs):
                    bits = side.width.try_eval(env)
                    if bits is not None and bits > 1:
                        found.append(
                            f"{where}: '{side.render()}' is {bits} bits but "
                            f"'{current.op}' expects 1 -- use a reduction "
                            f"(.ror()) or compare explicitly"
                        )
            walk(current.lhs)
            walk(current.rhs)
        elif isinstance(current, Unary):
            if current.op == "!":
                bits = current.operand.width.try_eval(env)
                if bits is not None and bits > 1:
                    found.append(
                        f"{where}: '{current.operand.render()}' is {bits} bits "
                        f"but '!' expects 1 -- use .rnor() or compare explicitly"
                    )
            walk(current.operand)
        elif isinstance(current, Cond):
            walk(current.sel)
            walk(current.then)
            walk(current.other)
        elif isinstance(current, Concat):
            for part in current.parts:
                walk(part)
        elif isinstance(current, (Cast, Repl)):
            walk(current.operand)
    walk(node)
    return found


def check_assign_width(target: Expr, value: Expr, env, where: str) -> str | None:
    """Return a message when assigning *value* to *target* loses bits.

    Only provable mismatches are reported; symbolic widths that merely differ
    in spelling are left alone. Fills and unsized literals are context-sized
    by SV and so are always acceptable.
    """
    if isinstance(value, Fill):
        return None
    if isinstance(value, Literal) and not value.sized:
        lhs_bits = target.width.try_eval(env)
        if lhs_bits is not None and value.value.bit_length() > lhs_bits:
            return (
                f"{where}: literal {value.value} needs "
                f"{value.value.bit_length()} bits but target is {lhs_bits}"
            )
        return None
    lhs_bits = target.width.try_eval(env)
    rhs_bits = value.width.try_eval(env)
    if lhs_bits is None or rhs_bits is None or lhs_bits == rhs_bits:
        return None
    verb = "truncates" if rhs_bits > lhs_bits else "zero-extends"
    return (
        f"{where}: assignment {verb} -- target is {lhs_bits} bits, "
        f"source {rhs_bits} bits ({value.render()})"
    )
