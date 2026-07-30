# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa
# Purpose: Generate synthesizable SystemVerilog from Python
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""svsherpa -- synthesizable SystemVerilog, written in Python.

A thin emitter, not an elaboration framework. SystemVerilog keeps the
semantics; Python supplies parameterization, loops, width algebra and checking.
The output is meant to be read, reviewed and committed like hand-written RTL.

    from svsherpa import *

    m = Module("counter", subsystem="common", purpose="Enabled binary counter")
    WIDTH = m.param("WIDTH", 8)
    clk, rst_n, en = m.input("clk"), m.input("rst_n"), m.input("en")
    count = m.output("count", WIDTH)

    m.always_ff(clk, rst_n,
        reset = [count.set(ZERO)],
        body  = [If(en, count.set(count + 1))],
    )
    print(m.emit())

What the library checks, so the tools do not have to:

* provable width mismatches on assignment
* multiple drivers, and assignment to an input port
* ``always_comb`` paths that infer a latch
* instance connections against the target module's real ports
* reserved words and duplicate identifiers

What it deliberately does not do: infer your intent. Blocking vs non-blocking
comes from the enclosing process, so it is always right; everything else is
written the way you would write it in SV.
"""

from __future__ import annotations

from .errors import SvDriverError, SvError, SvNameError, SvWarning, SvWidthError
from .expr import (
    B,
    C,
    Concat,
    Cond,
    Expr,
    Fill,
    FuncCall,
    Literal,
    ONES,
    Raw as RawExpr,
    Repl,
    SysCall,
    ZERO,
    clog2,
    clog2_expr,
    lift,
    mux,
    same,
)
from .generate import GenFor, GenIf, GenVar, genvar_expr, raw_expr
from .header import ModuleDoc
from .instance import Instance
from .module import Module
from .procs import AlwaysComb, AlwaysFF, AlwaysLatch, ContinuousAssign, ResetSpec
from .signals import (
    IN,
    INOUT,
    OUT,
    Inout,
    Input,
    Logic,
    LocalParam,
    Output,
    Param,
    Port,
    Signal,
    Wire,
)
from .stmt import Block, Case, CaseArm, Comment, EmitCtx, If, Raw, Stmt
from .symint import SymInt, width_of, widths_conflict
from .tools import Report, ToolResult, verible_lint, verify, verilator_lint, yosys_synth
from .svtypes import Enum, EnumMember, FieldRef, Struct, StructPort, StructSignal

__version__ = "0.1.0"

__all__ = [
    # building blocks
    "Module",
    "ModuleDoc",
    "Signal",
    "Port",
    "Param",
    "LocalParam",
    "Logic",
    "Wire",
    "Input",
    "Output",
    "Inout",
    "IN",
    "OUT",
    "INOUT",
    # expressions
    "Expr",
    "C",
    "B",
    "ZERO",
    "ONES",
    "Fill",
    "Literal",
    "Concat",
    "Repl",
    "Cond",
    "mux",
    "SysCall",
    "FuncCall",
    "RawExpr",
    "clog2",
    "clog2_expr",
    "lift",
    "same",
    "width_of",
    "widths_conflict",
    "SymInt",
    # statements
    "Stmt",
    "If",
    "Case",
    "CaseArm",
    "Block",
    "Comment",
    "Raw",
    "EmitCtx",
    # processes
    "AlwaysComb",
    "AlwaysFF",
    "AlwaysLatch",
    "ContinuousAssign",
    "ResetSpec",
    # structure
    "Instance",
    "GenFor",
    "GenIf",
    "GenVar",
    "genvar_expr",
    "raw_expr",
    # types
    "Enum",
    "EnumMember",
    "Struct",
    "StructSignal",
    "StructPort",
    "FieldRef",
    # verification
    "verify",
    "verilator_lint",
    "verible_lint",
    "yosys_synth",
    "Report",
    "ToolResult",
    # errors
    "SvError",
    "SvWidthError",
    "SvDriverError",
    "SvNameError",
    "SvWarning",
]
