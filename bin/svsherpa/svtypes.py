# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.svtypes
# Purpose: User-defined types -- packed enums and packed structs
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Packed enums and packed structs.

``Enum`` computes its own width and member encodings, so switching an FSM from
binary to one-hot is a one-word change rather than a rewrite::

    st = Enum("state_t", ["S0", "S1", "S2", "S3"], encoding="onehot")
    st.S0                       # 4'b0001
    Enum(..., encoding="gray")  # single-bit transitions

``Struct`` names the fields inside a vector. Fields are packed MSB-first in
declaration order, matching SystemVerilog, and field access is by attribute::

    cmd_t = Struct("cmd_pkt_t", [("valid", 1), ("opcode", 3), ("data", 16)])
    cmd = m.logic("cmd_q", cmd_t)
    cmd.opcode                  # cmd_q.opcode, 3 bits wide
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from .errors import SvError, check_identifier
from .expr import Expr, Literal, P_ATOM, width_of
from .signals import Signal
from .symint import SymInt

ENCODINGS = ("binary", "onehot", "gray")


def _encode(names: Sequence[str], encoding: str) -> tuple[list[int], int]:
    """Member values and the base width they require."""
    count = len(names)
    if count == 0:
        raise SvError("enum needs at least one member")
    if encoding == "binary":
        width = max(1, (count - 1).bit_length())
        return list(range(count)), width
    if encoding == "onehot":
        return [1 << i for i in range(count)], count
    if encoding == "gray":
        width = max(1, (count - 1).bit_length())
        return [i ^ (i >> 1) for i in range(count)], width
    raise SvError(f"unknown encoding {encoding!r}; expected one of {ENCODINGS}")


@dataclass(frozen=True, eq=False)
class EnumMember(Expr):
    """A reference to one enum member, e.g. ``S0``."""

    name: str
    value: int
    _width: SymInt

    @property
    def width(self) -> SymInt:
        return self._width

    def render(self, prec: int = 0) -> str:
        return self.name


class Enum:
    """A ``typedef enum`` with computed member encodings."""

    def __init__(
        self,
        name: str,
        members: Sequence[str] | dict,
        *,
        encoding: str = "binary",
        base: str = "logic",
    ):
        check_identifier(name, "type name")
        self.name = name
        self.base = base
        self.encoding = encoding
        if isinstance(members, dict):
            names = list(members.keys())
            values = list(members.values())
            width = max(1, max(values).bit_length()) if values else 1
        else:
            names = list(members)
            values, width = _encode(names, encoding)
        for member in names:
            check_identifier(member, "enum member")
        self.members = tuple(zip(names, values))
        self.width = SymInt.lit(width)
        self._by_name = {
            member: EnumMember(member, value, self.width)
            for member, value in self.members
        }

    def __getattr__(self, item: str) -> EnumMember:
        try:
            return self._by_name[item]
        except KeyError as exc:
            raise AttributeError(
                f"enum {self.name} has no member {item!r}; "
                f"members are {', '.join(self._by_name)}"
            ) from exc

    def __iter__(self):
        return iter(self._by_name.values())

    def __len__(self) -> int:
        return len(self.members)

    def declaration(self) -> list[str]:
        """The ``typedef enum ... { } name;`` lines."""
        bits = self.width.try_eval({}) or 1
        span = f" [{bits - 1}:0]" if bits > 1 else ""
        pad = max(len(m) for m, _ in self.members)
        lines = [f"typedef enum {self.base}{span} {{"]
        for idx, (member, value) in enumerate(self.members):
            comma = "," if idx < len(self.members) - 1 else ""
            literal = f"{bits}'b{value:0{bits}b}"
            lines.append(f"    {member:<{pad}} = {literal}{comma}")
        lines.append(f"}} {self.name};")
        return lines


class EnumSignal(Signal):
    """A signal declared with an enum typedef, e.g. ``state_t state;``.

    Carries the enum's width so comparisons and assignments against members
    width-check correctly -- otherwise every ``state <= S0`` looks like a
    truncation onto a 1-bit target.
    """

    def __init__(self, name: str, enum: "Enum", **kwargs):
        Signal.__init__(self, name, 1, kind=enum.name, **kwargs)
        object.__setattr__(self, "_enum", enum)

    @property
    def width(self) -> SymInt:
        return self._enum.width

    def declaration(self) -> str:
        return f"{self._enum.name} {self.name}"

    def decl_fields(self) -> tuple[str, str, str, str]:
        return ("", self._enum.name, "", self.name)


class EnumPort(EnumSignal):
    """A module port declared with an enum typedef."""

    def __init__(self, name: str, enum: "Enum", direction: str = "input", **kwargs):
        EnumSignal.__init__(self, name, enum, **kwargs)
        object.__setattr__(self, "direction", direction)

    def declaration(self) -> str:
        return f"{self.direction} {self._enum.name} {self.name}"

    def decl_fields(self) -> tuple[str, str, str, str]:
        return (self.direction, self._enum.name, "", self.name)


@dataclass(frozen=True, eq=False)
class FieldRef(Expr):
    """``sig.field`` -- a struct member select."""

    operand: Expr
    field: str
    _width: SymInt

    @property
    def width(self) -> SymInt:
        return self._width

    def is_lvalue(self) -> bool:
        return self.operand.is_lvalue()

    def render(self, prec: int = 0) -> str:
        return f"{self.operand.render(P_ATOM)}.{self.field}"


# Attributes on Signal that a struct field must not shadow.
_SIGNAL_ATTRS = frozenset(dir(Signal("_probe", 1)))


class Struct:
    """A ``typedef struct packed`` whose fields are accessed by name."""

    def __init__(self, name: str, fields: Sequence[tuple], *, base: str = "logic"):
        check_identifier(name, "type name")
        self.name = name
        self.base = base
        self.fields: list[tuple[str, SymInt, str]] = []
        for entry in fields:
            fname, fwidth, *rest = entry
            check_identifier(fname, "struct field")
            if fname in _SIGNAL_ATTRS:
                raise SvError(
                    f"struct field {fname!r} collides with a Signal attribute; "
                    f"rename the field so `sig.{fname}` is unambiguous"
                )
            self.fields.append((fname, width_of(fwidth), rest[0] if rest else ""))

    @property
    def width(self) -> SymInt:
        total = SymInt.lit(0)
        for _, fwidth, _ in self.fields:
            total = total + fwidth
        return total

    def field_width(self, name: str) -> SymInt:
        for fname, fwidth, _ in self.fields:
            if fname == name:
                return fwidth
        raise SvError(f"struct {self.name} has no field {name!r}")

    def declaration(self) -> list[str]:
        """The ``typedef struct packed { ... } name;`` lines, MSB first.

        Each field is annotated with the bit range it occupies, which is the
        detail that makes a packed struct reviewable against a spec.
        """
        rendered = [
            ("" if fwidth.try_eval({}) == 1 else f"[{(fwidth - 1).render()}:0]",
             fname, comment, fwidth.try_eval({}))
            for fname, fwidth, comment in self.fields
        ]
        span_pad = max((len(span) for span, _, _, _ in rendered), default=0)
        name_pad = max((len(name) for _, name, _, _ in rendered), default=0)

        total = self.width.try_eval({})
        cursor = total
        lines = ["typedef struct packed {"]
        for span, fname, comment, bits in rendered:
            decl = f"    logic {span:<{span_pad}} {fname + ';':<{name_pad + 1}}".rstrip()
            note = comment
            if cursor is not None and bits is not None:
                high, low = cursor - 1, cursor - bits
                rng = f"[{high}]" if bits == 1 else f"[{high}:{low}]"
                note = f"{rng}  {comment}".rstrip()
                cursor = low
            lines.append(f"{decl}  // {note}" if note else decl)
        suffix = f"  // {total} bits total" if total is not None else ""
        lines.append(f"}} {self.name};{suffix}")
        return lines


class StructSignal(Signal):
    """A signal whose type is a :class:`Struct`, giving attribute field access."""

    def __init__(self, name: str, struct: Struct, **kwargs):
        Signal.__init__(self, name, 1, kind=struct.name, **kwargs)
        object.__setattr__(self, "_struct", struct)

    @property
    def width(self) -> SymInt:
        return self._struct.width

    def declaration(self) -> str:
        return f"{self._struct.name} {self.name}"

    def decl_fields(self) -> tuple[str, str, str, str]:
        return ("", self._struct.name, "", self.name)

    def __getattr__(self, item: str) -> FieldRef:
        struct = self.__dict__.get("_struct") or object.__getattribute__(self, "_struct")
        try:
            width = struct.field_width(item)
        except SvError as exc:
            raise AttributeError(str(exc)) from exc
        return FieldRef(self, item, width)


class StructPort(StructSignal):
    """A module port whose type is a :class:`Struct`."""

    def __init__(self, name: str, struct: Struct, direction: str = "input", **kwargs):
        StructSignal.__init__(self, name, struct, **kwargs)
        object.__setattr__(self, "direction", direction)

    def declaration(self) -> str:
        return f"{self.direction} {self._struct.name} {self.name}"

    def decl_fields(self) -> tuple[str, str, str, str]:
        return (self.direction, self._struct.name, "", self.name)


def enum_literal(member: EnumMember, width: SymInt | None = None) -> Expr:
    """The numeric literal behind an enum member, when the raw value is needed."""
    bits = (width or member.width).try_eval({}) or 1
    return Literal(member.value, SymInt.lit(bits), sized=True, base="b")
