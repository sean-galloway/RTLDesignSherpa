# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.module
# Purpose: The Module builder -- declarations, body, and emission
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""The module builder.

``Module`` is the one mutable object in the library: you declare into it, then
emit. Everything it holds -- expressions, statements -- is immutable, so nothing
you build can be changed behind your back.

Declarations are emitted in dependency order (typedefs, then localparams, then
signals, then body) so generated files satisfy declare-before-use, which the
repo's ``check_sv_decl_order.py`` enforces.

    m = Module("counter_bin", subsystem="common", purpose="Binary counter")
    WIDTH = m.param("WIDTH", 5)
    clk   = m.input("clk")
    rst_n = m.input("rst_n")
    count = m.output("count", WIDTH)

    m.always_ff(clk, rst_n, reset=[count.set(ZERO)], body=[count.set(count + 1)])
    print(m.emit())
"""

from __future__ import annotations

from pathlib import Path
from typing import Sequence

from .errors import SvError, SvWarning, check_identifier
from .expr import Expr, width_of
from .header import ModuleDoc, doc_banner, spdx_header
from .instance import Instance
from .procs import AlwaysComb, AlwaysFF, AlwaysLatch, ContinuousAssign, ResetSpec
from .signals import IN, INOUT, OUT, Param, Port, Signal
from .stmt import Comment, EmitCtx, Raw, Stmt, _as_stmts
from .symint import SymInt
from .svtypes import Enum, EnumPort, EnumSignal, Struct, StructPort, StructSignal

TAB = "    "


class Module:
    """A synthesizable SystemVerilog module under construction."""

    def __init__(
        self,
        name: str,
        *,
        purpose: str = "",
        subsystem: str = "common",
        author: str = "sean galloway",
        created: str = "",
        doc: ModuleDoc | None = None,
        reset_style: str = "macro",
        reset_macro: str = "ALWAYS_FF_RST",
        use_rst_asserted: bool = False,
        timescale: str = "1ns / 1ps",
        includes: Sequence[str] = ("reset_defs.svh",),
        tab: str = TAB,
    ):
        check_identifier(name, "module name")
        self.name = name
        self.purpose = purpose or name
        self.subsystem = subsystem
        self.author = author
        self.created = created
        self.doc = doc
        self.reset_style = reset_style
        self.reset_macro = reset_macro
        self.use_rst_asserted = use_rst_asserted
        self.timescale = timescale
        # A macro-style reset is meaningless without the macro definitions.
        self.includes = list(includes) if reset_style == "macro" else [
            inc for inc in includes if inc != "reset_defs.svh"
        ]
        self.tab = tab

        self.params: list[Param] = []
        self.localparams: list[Param] = []
        self.ports: list[Port] = []
        self.signals: list[Signal] = []
        self.typedefs: list = []
        self.body: list[Stmt] = []
        self._names: set[str] = set()
        # Diagnostics are split by origin so that emitting twice does not
        # duplicate them: structural checks accumulate, emission-time checks
        # are replaced on every emit.
        self._structural: list[SvWarning] = []
        self._emitted: list[SvWarning] = []

    @property
    def warnings(self) -> list[SvWarning]:
        """Structural and emission-time diagnostics, de-duplicated."""
        seen: dict[tuple, SvWarning] = {}
        for warning in (*self._structural, *self._emitted):
            seen.setdefault((warning.kind, warning.message), warning)
        return list(seen.values())

    # ------------------------------------------------------------------ naming
    def _claim(self, name: str, what: str) -> None:
        if name in self._names:
            raise SvError(f"duplicate {what} name {name!r} in module {self.name}")
        self._names.add(name)

    @property
    def env(self) -> dict:
        """Parameter defaults, used to evaluate widths for checking."""
        out: dict = {}
        for param in (*self.params, *self.localparams):
            value = param.value
            if isinstance(value, int) and not isinstance(value, bool):
                out[param.name] = value
            elif isinstance(value, SymInt):
                resolved = value.try_eval(out)
                if resolved is not None:
                    out[param.name] = resolved
            elif isinstance(value, Expr):
                resolved = width_of(value).try_eval(out)
                if resolved is not None:
                    out[param.name] = resolved
        return out

    # ------------------------------------------------------------- declarations
    def param(self, name: str, value=None, ptype: str = "int", *, comment: str = "") -> Param:
        """Add a ``parameter`` to the module header."""
        self._claim(name, "parameter")
        param = Param(name, value, ptype, comment=comment)
        self.params.append(param)
        return param

    def localparam(self, name: str, value, ptype: str = "int", *, comment: str = "") -> Param:
        """Add a ``localparam``, emitted at the top of the module body."""
        self._claim(name, "localparam")
        param = Param(name, value, ptype, comment=comment, is_local=True)
        self.localparams.append(param)
        return param

    def _add_port(self, name, direction, width, kind, unpacked, signed, comment):
        self._claim(name, "port")
        if isinstance(width, Struct):
            port = StructPort(name, width, direction, comment=comment)
        elif isinstance(width, Enum):
            port = EnumPort(name, width, direction, comment=comment)
        else:
            port = Port(
                name, direction, _type_width(width),
                unpacked=unpacked, kind=_type_kind(width, kind),
                signed=signed, comment=comment,
            )
        self.ports.append(port)
        return port

    def input(self, name: str, width=1, *, kind="logic", unpacked=None,
              signed=False, comment="") -> Port:
        """Add an ``input`` port."""
        return self._add_port(name, IN, width, kind, unpacked, signed, comment)

    def output(self, name: str, width=1, *, kind="logic", unpacked=None,
               signed=False, comment="") -> Port:
        """Add an ``output`` port."""
        return self._add_port(name, OUT, width, kind, unpacked, signed, comment)

    def inout(self, name: str, width=1, *, kind="logic", unpacked=None,
              signed=False, comment="") -> Port:
        """Add an ``inout`` port."""
        return self._add_port(name, INOUT, width, kind, unpacked, signed, comment)

    def logic(self, name: str, width=1, *, unpacked=None, signed=False,
              comment="") -> Signal:
        """Declare an internal ``logic`` signal.

        *width* accepts an int, a parameter expression, an :class:`Enum` or a
        :class:`Struct`.
        """
        self._claim(name, "signal")
        if isinstance(width, Struct):
            sig = StructSignal(name, width, comment=comment)
        elif isinstance(width, Enum):
            sig = EnumSignal(name, width, comment=comment)
        else:
            sig = Signal(
                name, _type_width(width), unpacked=unpacked,
                kind=_type_kind(width, "logic"), signed=signed, comment=comment,
            )
        self.signals.append(sig)
        return sig

    def wire(self, name: str, width=1, **kwargs) -> Signal:
        """Declare a ``wire``. Use with :meth:`assign` at the point of use."""
        self._claim(name, "signal")
        sig = Signal(name, _type_width(width), kind="wire", **kwargs)
        self.signals.append(sig)
        return sig

    def mem(self, name: str, width, depth, *, comment="") -> Signal:
        """Declare an unpacked memory array: ``logic [W-1:0] name [DEPTH];``"""
        return self.logic(name, width, unpacked=[depth], comment=comment)

    def typedef(self, type_obj) -> object:
        """Register an :class:`Enum` or :class:`Struct` for emission."""
        if not isinstance(type_obj, (Enum, Struct)):
            raise SvError("typedef expects an Enum or Struct")
        self._claim(type_obj.name, "type")
        self.typedefs.append(type_obj)
        return type_obj

    def enum(self, name: str, members, *, encoding: str = "binary") -> Enum:
        """Define and register a packed enum in one step."""
        return self.typedef(Enum(name, members, encoding=encoding))

    def struct(self, name: str, fields) -> Struct:
        """Define and register a packed struct in one step."""
        return self.typedef(Struct(name, fields))

    # ------------------------------------------------------------------- body
    def add(self, *items) -> "Module":
        """Append statements to the module body."""
        self.body.extend(_as_stmts(items))
        return self

    def comment(self, text: str) -> "Module":
        """Append a ``//`` comment to the body."""
        self.body.append(Comment(text))
        return self

    def blank(self) -> "Module":
        """Append a blank line, for grouping."""
        self.body.append(Raw(""))
        return self

    def raw(self, text: str) -> "Module":
        """Append literal SV text. The escape hatch."""
        self.body.append(Raw(text))
        return self

    def assign(self, target: Expr, value, *, comment: str = "") -> "Module":
        """``assign target = value;``"""
        self.body.append(ContinuousAssign(target, value, comment))
        return self

    def always_comb(self, *body, comment: str = "") -> "Module":
        """``always_comb`` with blocking assignment."""
        self.body.append(AlwaysComb(*body, comment=comment))
        return self

    def always_ff(
        self,
        clock: Expr,
        rst=None,
        *,
        reset: Sequence[Stmt] | None = None,
        body: Sequence[Stmt] | None = None,
        comment: str = "",
        posedge: bool = True,
    ) -> "Module":
        """``always_ff`` with non-blocking assignment.

        With *rst* and *reset*, emits the module's configured reset style.
        Without them, emits a plain ``@(posedge clk)`` block -- which is what an
        inferred memory write port wants.
        """
        spec = None
        if rst is not None:
            spec = ResetSpec(
                signal=rst,
                style=self.reset_style,
                macro=self.reset_macro,
                use_rst_asserted=self.use_rst_asserted,
            )
        stmts = body if body is not None else ()
        self.body.append(
            AlwaysFF(
                clock, *_as_stmts([stmts]),
                reset=spec, reset_body=reset, comment=comment, posedge=posedge,
            )
        )
        return self

    def always_latch(self, *body, comment: str = "") -> "Module":
        self.body.append(AlwaysLatch(*body, comment=comment))
        return self

    def instance(
        self,
        module_name,
        inst_name: str,
        ports=None,
        params=None,
        *,
        comment: str = "",
    ) -> Instance:
        """Instantiate a sub-module with named connections.

        *module_name* may be a :class:`Module`, in which case connections are
        validated against its real port list.
        """
        of = module_name if isinstance(module_name, Module) else None
        name = of.name if of is not None else module_name
        inst = Instance(name, inst_name, ports, params, comment=comment, of=of)
        self.body.append(inst)
        return inst

    # ------------------------------------------------------------------ checks
    def check(self) -> list[SvWarning]:
        """Run structural checks and return every accumulated warning."""
        self._structural = []
        self._check_drivers()
        self._check_unused()
        # Emission performs the width and latch checks; run it and keep them.
        self.emit()
        return self.warnings

    def _check_drivers(self) -> None:
        """Reject a signal driven from more than one process or assign."""
        seen: dict[str, str] = {}
        for item in self.body:
            kind = type(item).__name__
            # Dedupe within one block: a reset arm and a body arm both driving
            # the same register is exactly right, not a double drive.
            for name in dict.fromkeys(item.targets()):
                previous = seen.get(name)
                if previous is not None:
                    raise SvError(
                        f"{self.name}: '{name}' is driven by both {previous} and "
                        f"{kind}; a signal needs exactly one driver"
                    )
                seen[name] = kind
        inputs = {p.name for p in self.ports if p.direction == IN}
        driven = set(seen)
        clash = inputs & driven
        if clash:
            raise SvError(
                f"{self.name}: input port(s) {', '.join(sorted(clash))} are "
                f"assigned inside the module"
            )
        undriven = [
            p.name for p in self.ports if p.direction == OUT and p.name not in driven
        ]
        for name in undriven:
            self._structural.append(
                SvWarning("undriven-output", f"output '{name}' is never assigned",
                          self.name)
            )

    def _check_unused(self) -> None:
        """Flag declared signals that never appear in the emitted body."""
        text = "\n".join(self._body_lines(EmitCtx(indent=1, env=self.env)))
        for sig in self.signals:
            if sig.name not in text:
                self._structural.append(
                    SvWarning("unused-signal", f"signal '{sig.name}' is never used",
                              self.name)
                )

    # ---------------------------------------------------------------- emission
    def _body_lines(self, ctx: EmitCtx) -> list[str]:
        """Emit body items, separating blocks with a blank line.

        Runs of one-line statements (a group of ``assign``s) stay together;
        anything multi-line gets air around it, the way hand-written RTL reads.
        """
        lines: list[str] = []
        previous_block = False
        for item in self.body:
            chunk = item.emit(ctx)
            if not chunk:
                continue
            is_block = len(chunk) > 1
            explicit_blank = chunk == [""]
            if lines and (is_block or previous_block) and not explicit_blank:
                if lines[-1].strip():
                    lines.append("")
            lines.extend(chunk)
            previous_block = is_block
        return lines

    def port_lines(self) -> list[str]:
        """Column-aligned port declarations for the module header."""
        if not self.ports:
            return []
        rows = [p.decl_fields() for p in self.ports]
        out = []
        for idx, cells in enumerate(rows):
            comma = "," if idx < len(rows) - 1 else ""
            line = f"{self.tab}{_align(cells, rows)}{comma}"
            comment = self.ports[idx].comment
            out.append(f"{line}  // {comment}" if comment else line)
        return out

    def param_lines(self) -> list[str]:
        """Column-aligned parameter declarations for the module header."""
        if not self.params:
            return []
        rows = [p.decl_fields() for p in self.params]
        type_pad = max(len(r[0]) for r in rows)
        name_pad = max(len(r[1]) for r in rows)
        out = []
        for idx, (ptype, name, default) in enumerate(rows):
            comma = "," if idx < len(rows) - 1 else ""
            text = f"{self.tab}parameter {ptype:<{type_pad}} {name:<{name_pad}}"
            if default:
                text = f"{text} = {default}"
            comment = self.params[idx].comment
            line = f"{text.rstrip()}{comma}"
            out.append(f"{line}  // {comment}" if comment else line)
        return out

    def emit(self) -> str:
        """Render the complete ``.sv`` file."""
        ctx = EmitCtx(indent=1, tab=self.tab, env=self.env)
        body = self._body_lines(ctx)
        # Width and latch diagnostics surface during emission. Replace rather
        # than append, so emit() stays idempotent.
        self._emitted = [
            SvWarning(kind, message, self.name) for kind, message in ctx.warnings
        ]

        out: list[str] = []
        out.extend(
            spdx_header(
                self.name, self.purpose, subsystem=self.subsystem,
                author=self.author, created=self.created,
            )
        )
        out.append("")
        if self.timescale:
            out.append(f"`timescale {self.timescale}")
            out.append("")
        if self.doc is not None:
            out.extend(doc_banner(self.name, self.doc, self.params, self.ports))
            out.append("")
        # Only include reset_defs.svh when a macro-style reset actually uses
        # it. A module of pure combinatorial logic should not drag in an
        # include, which would otherwise break a standalone lint.
        body_text = "\n".join(body)
        includes = [
            inc for inc in self.includes
            if inc != "reset_defs.svh" or f"`{self.reset_macro}" in body_text
        ]
        for include in includes:
            out.append(f'`include "{include}"')
        if includes:
            out.append("")
        for type_obj in self.typedefs:
            out.extend(type_obj.declaration())
            out.append("")

        out.extend(self._module_header())

        inner: list[str] = []
        if self.localparams:
            for param in self.localparams:
                text = f"{self.tab}{param.declaration()};"
                inner.append(
                    f"{text}  // {param.comment}" if param.comment else text
                )
            inner.append("")
        if self.signals:
            inner.extend(self._signal_lines())
            inner.append("")
        inner.extend(body)

        out.extend(inner)
        out.append("")
        out.append(f"endmodule : {self.name}")
        out.append("")
        return "\n".join(out)

    def _module_header(self) -> list[str]:
        params = self.param_lines()
        ports = self.port_lines()
        if params and ports:
            return [f"module {self.name} #(", *params, ") (", *ports, ");"]
        if params:
            return [f"module {self.name} #(", *params, ") ();"]
        if ports:
            return [f"module {self.name} (", *ports, ");"]
        return [f"module {self.name} ();"]

    def _signal_lines(self) -> list[str]:
        rows = [s.decl_fields()[1:] for s in self.signals]
        out = []
        for idx, cells in enumerate(rows):
            line = f"{self.tab}{_align(cells, rows)};"
            comment = self.signals[idx].comment
            out.append(f"{line}  // {comment}" if comment else line)
        return out

    def write(self, path) -> Path:
        """Write the module to *path* (a file, or a directory to name it in)."""
        target = Path(path)
        if target.is_dir():
            target = target / f"{self.name}.sv"
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(self.emit())
        return target

    def __str__(self) -> str:
        return self.emit()

    def __repr__(self) -> str:
        return (
            f"<Module {self.name}: {len(self.ports)} ports, "
            f"{len(self.params)} params, {len(self.body)} items>"
        )


def _align(cells: Sequence[str], rows: Sequence[Sequence[str]]) -> str:
    """Join *cells* into a column-aligned row, skipping all-empty columns.

    A column that is empty for every row -- no packed range anywhere, say --
    is dropped entirely rather than padded, so scalar-only declarations do not
    carry a stray gap.
    """
    parts = []
    for index, cell in enumerate(cells):
        pad = max(len(row[index]) for row in rows)
        if pad == 0:
            continue
        parts.append(cell.ljust(pad) if index < len(cells) - 1 else cell)
    return " ".join(parts).rstrip()


def _type_width(width):
    """A width, an Enum (use its base width) or a Struct (handled elsewhere)."""
    if isinstance(width, Enum):
        return 1  # the typedef carries the width; the signal is just the type
    return width


def _type_kind(width, default: str) -> str:
    """The declared type name: a typedef for an Enum, else the default."""
    if isinstance(width, Enum):
        return width.name
    return default
