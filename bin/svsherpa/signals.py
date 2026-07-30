# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.signals
# Purpose: Signals, ports, parameters and their declarations
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Signals, ports and parameters.

Declarations carry packed and unpacked dimensions separately, matching the way
SystemVerilog distinguishes them::

    logic [WIDTH-1:0]            data;          # packed  = (WIDTH,)
    logic [CHANNELS-1:0][WIDTH-1:0] q;          # packed  = (CHANNELS, WIDTH)
    logic [DATA_WIDTH-1:0]       mem [DEPTH];   # unpacked = (DEPTH,)

Indexing is dimension-aware, so ``q[i]`` on that second declaration is a
``WIDTH``-bit expression rather than a single bit -- the mistake that packed 2-D
ports invite.

Assignment is written ``sig.set(value)`` and deliberately does *not* name the
operator. The enclosing process decides: ``always_ff`` emits ``<=``,
``always_comb`` emits ``=``, module scope emits ``assign``. Choosing the wrong
one is a classic RTL bug, and here it is not expressible.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Sequence

from .errors import SvError, check_identifier
from .expr import P_ATOM, Expr, ExprLike, width_of
from .symint import SymInt

# Port directions, spelled as SystemVerilog spells them.
IN = "input"
OUT = "output"
INOUT = "inout"


def _dims(value) -> tuple[SymInt, ...]:
    """Normalise a width or dimension list into a tuple of SymInts."""
    if value is None:
        return ()
    if isinstance(value, (list, tuple)):
        return tuple(width_of(v) for v in value)
    return (width_of(value),)


def _render_packed(dims: Sequence[SymInt]) -> str:
    """``[A-1:0][B-1:0]`` for the packed dimensions, or '' for a scalar."""
    out = []
    for dim in dims:
        known = dim.try_eval({})
        if known == 1:
            continue  # a 1-bit packed dimension is just a scalar
        out.append(f"[{(dim - 1).render()}:0]")
    return "".join(out)


def _render_unpacked(dims: Sequence[SymInt]) -> str:
    """``[DEPTH]`` for unpacked dimensions."""
    return "".join(f"[{d.render()}]" for d in dims)


@dataclass(frozen=True, eq=False)
class Signal(Expr):
    """A named signal: an expression that can also be assigned and declared."""

    name: str
    packed: tuple[SymInt, ...] = ()
    unpacked: tuple[SymInt, ...] = ()
    kind: str = "logic"          # logic | wire | reg | a typedef name
    signed: bool = False         # type: ignore[assignment]
    comment: str = ""

    def __init__(
        self,
        name: str,
        width=1,
        *,
        unpacked=None,
        kind: str = "logic",
        signed: bool = False,
        comment: str = "",
    ):
        check_identifier(name, "signal name")
        object.__setattr__(self, "name", name)
        object.__setattr__(self, "packed", _dims(width))
        object.__setattr__(self, "unpacked", _dims(unpacked))
        object.__setattr__(self, "kind", kind)
        object.__setattr__(self, "signed", signed)
        object.__setattr__(self, "comment", comment)

    # -------------------------------------------------------------- expression
    @property
    def width(self) -> SymInt:
        """Total packed bit count (the product of packed dimensions)."""
        total = SymInt.lit(1)
        for dim in self.packed:
            total = total * dim
        return total

    @property
    def elem_width(self) -> SymInt:
        """Width of one element after indexing the outermost dimension.

        Unpacked dimensions are outermost, so indexing ``logic [7:0] mem [16]``
        yields the full 8-bit word. Only once the unpacked dimensions are used
        up does indexing start peeling packed dimensions.
        """
        if self.unpacked:
            return self.width
        if len(self.packed) <= 1:
            return SymInt.lit(1)
        total = SymInt.lit(1)
        for dim in self.packed[1:]:
            total = total * dim
        return total

    def render(self, prec: int = 0) -> str:
        return self.name

    # ---------------------------------------------------------------- indexing
    def __getitem__(self, key) -> Expr:
        """Index or slice, respecting array dimensions.

        For a multi-dimensional or unpacked signal, ``sig[i]`` selects an
        element of the outer dimension. For a plain vector it is a bit select,
        and ``sig[msb:lsb]`` is a part select.
        """
        is_array = len(self.packed) > 1 or bool(self.unpacked)
        if is_array and not isinstance(key, slice):
            return ArrayIndex(self, width_of(key), self.elem_width)
        return super().__getitem__(key)

    # -------------------------------------------------------------- assignment
    def is_lvalue(self) -> bool:
        return True

    # ------------------------------------------------------------ declaration
    def declaration(self) -> str:
        """The SV declaration text, without the trailing semicolon."""
        parts = [self.kind]
        if self.signed:
            parts.append("signed")
        packed = _render_packed(self.packed)
        if packed:
            parts.append(packed)
        parts.append(self.name)
        text = " ".join(parts)
        unpacked = _render_unpacked(self.unpacked)
        return f"{text} {unpacked}" if unpacked else text

    def decl_fields(self) -> tuple[str, str, str, str]:
        """Declaration split into columns for alignment: dir, type, packed, name."""
        type_text = f"{self.kind} signed" if self.signed else self.kind
        name = self.name
        unpacked = _render_unpacked(self.unpacked)
        if unpacked:
            name = f"{name} {unpacked}"
        return ("", type_text, _render_packed(self.packed), name)


@dataclass(frozen=True, eq=False)
class Port(Signal):
    """A module port -- a signal plus a direction."""

    direction: str = IN

    def __init__(
        self,
        name: str,
        direction: str = IN,
        width=1,
        *,
        unpacked=None,
        kind: str = "logic",
        signed: bool = False,
        comment: str = "",
    ):
        if direction not in (IN, OUT, INOUT):
            raise SvError(f"unknown port direction {direction!r}")
        Signal.__init__(
            self,
            name,
            width,
            unpacked=unpacked,
            kind=kind,
            signed=signed,
            comment=comment,
        )
        object.__setattr__(self, "direction", direction)

    def declaration(self) -> str:
        return f"{self.direction} {super().declaration()}"

    def decl_fields(self) -> tuple[str, str, str, str]:
        _, type_text, packed, name = super().decl_fields()
        return (self.direction, type_text, packed, name)


@dataclass(frozen=True, eq=False)
class ArrayIndex(Expr):
    """``sig[i]`` where *sig* has array dimensions."""

    operand: Expr
    index: SymInt
    _width: SymInt

    @property
    def width(self) -> SymInt:
        return self._width

    def is_lvalue(self) -> bool:
        return self.operand.is_lvalue()

    def render(self, prec: int = 0) -> str:
        return f"{self.operand.render(P_ATOM)}[{self.index.render()}]"


@dataclass(frozen=True, eq=False)
class Param(Expr):
    """A module parameter. Usable as a width and as an expression."""

    name: str
    value: object = None
    ptype: str = "int"
    comment: str = ""
    is_local: bool = False

    def __init__(
        self,
        name: str,
        value=None,
        ptype: str = "int",
        *,
        comment: str = "",
        is_local: bool = False,
    ):
        check_identifier(name, "parameter name")
        object.__setattr__(self, "name", name)
        object.__setattr__(self, "value", value)
        object.__setattr__(self, "ptype", ptype)
        object.__setattr__(self, "comment", comment)
        object.__setattr__(self, "is_local", is_local)

    # `sym_name` is how expr._expr_to_sym recognises a parameter without
    # importing this module.
    @property
    def sym_name(self) -> str:
        return self.name

    @property
    def sym(self) -> SymInt:
        """This parameter as a width expression."""
        return SymInt.ref(self.name)

    @property
    def width(self) -> SymInt:
        # Parameters are int-typed in practice; 32 bits matches SV's `int`.
        return SymInt.lit(32)

    def render(self, prec: int = 0) -> str:
        return self.name

    def default_text(self) -> str:
        """The parameter's default value rendered as SV."""
        value = self.value
        if value is None:
            return ""
        if isinstance(value, bool):
            return "1" if value else "0"
        if isinstance(value, (SymInt, Expr)):
            return value.render()
        return str(value)

    def declaration(self) -> str:
        keyword = "localparam" if self.is_local else "parameter"
        text = f"{keyword} {self.ptype} {self.name}"
        default = self.default_text()
        return f"{text} = {default}" if default else text

    def decl_fields(self) -> tuple[str, str, str]:
        """Split into columns for alignment: type, name, default."""
        return (self.ptype, self.name, self.default_text())


def LocalParam(name: str, value, ptype: str = "int", *, comment: str = "") -> Param:
    """A ``localparam`` -- derived inside the module, not overridable."""
    return Param(name, value, ptype, comment=comment, is_local=True)


def Logic(name: str, width=1, **kwargs) -> Signal:
    """``logic`` declaration. The default signal kind for synthesizable RTL."""
    return Signal(name, width, kind="logic", **kwargs)


def Wire(name: str, width=1, **kwargs) -> Signal:
    """``wire`` declaration, for continuous assignment at the point of use."""
    return Signal(name, width, kind="wire", **kwargs)


def Input(name: str, width=1, **kwargs) -> Port:
    return Port(name, IN, width, **kwargs)


def Output(name: str, width=1, **kwargs) -> Port:
    return Port(name, OUT, width, **kwargs)


def Inout(name: str, width=1, **kwargs) -> Port:
    return Port(name, INOUT, width, **kwargs)
