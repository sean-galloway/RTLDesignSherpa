# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.instance
# Purpose: Sub-module instantiation with named connections
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Sub-module instantiation.

Connections are always named -- positional connection is not offered, because
it is the single easiest way to wire a design wrong and have it still compile.
Parameter and port lists are column-aligned so a large instance stays readable
and diffs stay narrow::

    SyncFIFO_Hsk #(
        .DEPTH      (FIFO_DEPTH),
        .DATA_WIDTH (DATA_WIDTH)
    ) u_fifo (
        .clk      (clk),
        .wr_valid (wr_valid[i]),
        .wr_data  (wr_data[i])
    );

When the instantiated module was itself built with :class:`~svsherpa.module.Module`,
pass it as *of* and the connection names are checked against its real port list,
so a typo or a missing port is an error here rather than an elaboration failure.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Mapping

from .errors import SvError, check_identifier
from .expr import Expr, lift
from .stmt import EmitCtx, Stmt


@dataclass
class Instance(Stmt):
    """An instantiation of *module_name* named *inst_name*."""

    module_name: str
    inst_name: str
    ports: dict
    params: dict = field(default_factory=dict)
    comment: str = ""
    of: object = None

    def __init__(
        self,
        module_name: str,
        inst_name: str,
        ports: Mapping | None = None,
        params: Mapping | None = None,
        *,
        comment: str = "",
        of=None,
    ):
        # `of` may be a Module, in which case it supplies the name and the
        # port list to validate against.
        if of is not None and not module_name:
            module_name = of.name
        check_identifier(inst_name, "instance name")
        self.module_name = module_name
        self.inst_name = inst_name
        # `None` is preserved: it marks a port deliberately left open, which
        # the validator accepts and the emitter renders as `.port ()`.
        self.ports = {
            k: (None if v is None else lift(v)) for k, v in (ports or {}).items()
        }
        self.params = dict(params or {})
        self.comment = comment
        self.of = of
        if of is not None:
            self._validate_against(of)

    def _validate_against(self, module) -> None:
        """Check connection and parameter names against the target module."""
        known_ports = {p.name for p in getattr(module, "ports", [])}
        if known_ports:
            unknown = set(self.ports) - known_ports
            if unknown:
                raise SvError(
                    f"{self.module_name} has no port(s) "
                    f"{', '.join(sorted(unknown))}; "
                    f"ports are {', '.join(sorted(known_ports))}"
                )
            missing = known_ports - set(self.ports)
            if missing:
                raise SvError(
                    f"instance {self.inst_name} of {self.module_name} leaves "
                    f"{', '.join(sorted(missing))} unconnected; connect "
                    f"explicitly (use None for an intentional open)"
                )
        known_params = {p.name for p in getattr(module, "params", [])}
        if known_params:
            unknown = set(self.params) - known_params
            if unknown:
                raise SvError(
                    f"{self.module_name} has no parameter(s) "
                    f"{', '.join(sorted(unknown))}"
                )

    def targets(self) -> list[str]:
        # Output connections are drivers, but which ports are outputs is only
        # known when `of` was supplied.
        if self.of is None:
            return []
        directions = {p.name: getattr(p, "direction", "input")
                      for p in getattr(self.of, "ports", [])}
        from .stmt import _root_name

        return [
            _root_name(conn)
            for name, conn in self.ports.items()
            if directions.get(name) == "output" and conn is not None
        ]

    def emit(self, ctx: EmitCtx) -> list[str]:
        pad = ctx.pad()
        lines = [f"{pad}// {self.comment}"] if self.comment else []

        head = self.module_name
        if self.params:
            keys = list(self.params)
            width = max(len(k) for k in keys)
            lines.append(f"{pad}{head} #(")
            for idx, key in enumerate(keys):
                comma = "," if idx < len(keys) - 1 else ""
                value = _render_conn(self.params[key])
                lines.append(f"{pad}{ctx.tab}.{key:<{width}} ({value}){comma}")
            lines.append(f"{pad}) {self.inst_name} (")
        else:
            lines.append(f"{pad}{head} {self.inst_name} (")

        keys = list(self.ports)
        if not keys:
            lines[-1] = lines[-1].rstrip("( ") + " ();"
            return lines
        width = max(len(k) for k in keys)
        for idx, key in enumerate(keys):
            comma = "," if idx < len(keys) - 1 else ""
            value = _render_conn(self.ports[key])
            lines.append(f"{pad}{ctx.tab}.{key:<{width}} ({value}){comma}")
        lines.append(f"{pad});")
        return lines


def _render_conn(value) -> str:
    """Render one connection; ``None`` means an intentionally open port."""
    if value is None:
        return ""
    if isinstance(value, Expr):
        return value.render()
    return str(value)
