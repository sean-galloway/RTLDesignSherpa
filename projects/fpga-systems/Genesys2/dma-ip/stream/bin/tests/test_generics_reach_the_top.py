# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Every build generic must exist as a parameter on the TOP module.

Vivado applies generics to the top. A generic naming a parameter the top does
NOT have is silently ignored -- Vivado only warns, and synthesis proceeds with
the RTL default. The bitstream then looks correct, programs fine, and is built
in a configuration nobody asked for.

This has now happened twice in this flow:

  - build-perf exported USE_AXI_MONITORS=0 for a long time with no generic in
    create_project.tcl to carry it, so EVERY Genesys 2 bitstream ever built
    shipped the full monitor CAMs -- including the "monitors-off" perf build.
    (The scar is commented in fpga/tcl/create_project.tcl.)
  - OBS_ENABLE_MON_TAPS was added to the Makefile and to create_project.tcl
    but not to stream_genesys2_top, so the obs-build would have synthesized
    with the observer taps OFF: a bitstream that measures nothing.

Both were invisible until something else happened to fail. The failure mode is
a silent wrong-configuration build costing a synthesis run, so it is worth a
test that runs in a second.

Three lists have to agree and none of them checks the others:
    fpga/tcl/create_project.tcl   what Vivado can set
    make/fpga_flow.mk             LINT_GENERICS -- what the lint gate checks
    rtl/stream_genesys2_top.sv    what the design actually has
"""

import re
from pathlib import Path

import pytest

_HERE = Path(__file__).resolve()
_STREAM = _HERE.parents[2]
_TCL = _STREAM / "fpga" / "tcl" / "create_project.tcl"
_TOP = _STREAM / "rtl" / "stream_genesys2_top.sv"
# Walk up to the repo root rather than counting parents: this file has moved
# directory depth before, and an index that silently resolves to the wrong
# place turns a real check into a FileNotFoundError nobody reads.
def _repo_root(start: Path) -> Path:
    for d in start.parents:
        if (d / "make" / "fpga_flow.mk").is_file():
            return d
    raise RuntimeError("repo root not found from " + str(start))


_FLOW = _repo_root(_HERE) / "make" / "fpga_flow.mk"


def _tcl_generics():
    return sorted(set(re.findall(r'lappend\s+generics\s+"([A-Z_0-9]+)=', _TCL.read_text())))


def _top_parameters():
    txt = _TOP.read_text()
    return set(re.findall(r"parameter\s+(?:type\s+|int\s+|bit\s+|logic\s*(?:\[[^\]]*\]\s*)?)?([A-Z_][A-Z_0-9]*)\s*=", txt))


def _lint_generics():
    return sorted(set(re.findall(r"-G([A-Z_0-9]+)=", _FLOW.read_text())))


def test_generics_exist_on_the_top_module():
    """A generic the top does not declare is silently ignored by Vivado."""
    missing = [g for g in _tcl_generics() if g not in _top_parameters()]
    assert not missing, (
        f"create_project.tcl sets generics the top module does not declare: "
        f"{missing}. Vivado will IGNORE them (warning only) and synthesize the "
        f"RTL default -- a bitstream built in a configuration nobody asked for. "
        f"Add the parameter to {_TOP.name} and forward it to stream_harness.")


def test_lint_gate_checks_the_same_generics_vivado_sets():
    """The lint gate must elaborate the configuration Vivado actually builds."""
    tcl = set(_tcl_generics())
    lint = set(_lint_generics())
    unchecked = sorted(tcl - lint)
    assert not unchecked, (
        f"these generics are set for Vivado but absent from LINT_GENERICS: "
        f"{unchecked}. The gate then elaborates a DIFFERENT configuration than "
        f"the one being synthesized, so an error only in the real config gets "
        f"through -- which is how the missing OBS_ENABLE_MON_TAPS parameter "
        f"survived to a bitstream build.")
