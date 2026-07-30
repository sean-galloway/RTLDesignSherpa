# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.errors
# Purpose: Exception and diagnostic types for the SV generator
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Diagnostics for svsherpa.

Two severities exist, and the distinction is deliberate:

``SvError``
    The design is wrong in a way that cannot produce correct RTL -- a width
    mismatch on a comparison, two drivers on one signal, a blocking assign in
    ``always_ff``. These raise immediately at build time.

``SvWarning``
    The design is legal but smells -- an incompletely assigned ``always_comb``
    (latch inference), an unused signal. These are collected on the module and
    reported together so a build is not stopped by style.
"""

from __future__ import annotations

from dataclasses import dataclass


class SvError(Exception):
    """Raised when the described hardware cannot be correct."""


class SvWidthError(SvError):
    """Raised when operand widths cannot be reconciled."""


class SvDriverError(SvError):
    """Raised on multiple drivers, or a driver in the wrong process kind."""


class SvNameError(SvError):
    """Raised on duplicate or illegal SystemVerilog identifiers."""


@dataclass(frozen=True)
class SvWarning:
    """A non-fatal diagnostic attached to a module."""

    kind: str
    message: str
    where: str = ""

    def __str__(self) -> str:
        loc = f" [{self.where}]" if self.where else ""
        return f"{self.kind}: {self.message}{loc}"


# SystemVerilog-1800 reserved words. Used to reject identifiers that would
# produce code that does not compile, which is a common failure mode when
# signal names are built up programmatically from data.
RESERVED = frozenset(
    """
    accept_on alias always always_comb always_ff always_latch and assert assign
    assume automatic before begin bind bins binsof bit break buf bufif0 bufif1
    byte case casex casez cell chandle checker class clocking cmos config const
    constraint context continue cover covergroup coverpoint cross deassign
    default defparam design disable dist do edge else end endcase endchecker
    endclass endclocking endconfig endfunction endgenerate endgroup endinterface
    endmodule endpackage endprimitive endprogram endproperty endspecify
    endsequence endtable endtask enum event eventually expect export extends
    extern final first_match for force foreach forever fork forkjoin function
    generate genvar global highz0 highz1 if iff ifnone ignore_bins
    illegal_bins implements implies import incdir include initial inout input
    inside instance int integer interconnect interface intersect join join_any
    join_none large let liblist library local localparam logic longint
    macromodule matches medium modport module nand negedge nettype new nexttime
    nmos nor noshowcancelled not notif0 notif1 null or output package packed
    parameter pmos posedge primitive priority program property protected pull0
    pull1 pulldown pullup pulsestyle_ondetect pulsestyle_onevent pure rand
    randc randcase randsequence rcmos real realtime ref reg reject_on release
    repeat restrict return rnmos rpmos rtran rtranif0 rtranif1 s_always
    s_eventually s_nexttime s_until s_until_with scalared sequence shortint
    shortreal showcancelled signed small soft solve specify specparam static
    string strong strong0 strong1 struct super supply0 supply1 sync_accept_on
    sync_reject_on table tagged task this throughout time timeprecision
    timeunit tran tranif0 tranif1 tri tri0 tri1 triand trior trireg type
    typedef union unique unique0 unsigned until until_with untyped use uwire
    var vectored virtual void wait wait_order wand weak weak0 weak1 while
    wildcard wire with within wor xnor xor
    """.split()
)


def check_identifier(name: str, what: str = "identifier") -> str:
    """Validate *name* as a legal, non-reserved SV identifier.

    Returns the name unchanged so this can be used inline in constructors.
    """
    if not name:
        raise SvNameError(f"empty {what}")
    if name in RESERVED:
        raise SvNameError(f"{what} {name!r} is a SystemVerilog reserved word")
    head, *rest = name
    if not (head.isalpha() or head == "_"):
        raise SvNameError(
            f"{what} {name!r} must start with a letter or underscore"
        )
    for ch in rest:
        if not (ch.isalnum() or ch == "_"):
            raise SvNameError(f"{what} {name!r} contains illegal character {ch!r}")
    return name
