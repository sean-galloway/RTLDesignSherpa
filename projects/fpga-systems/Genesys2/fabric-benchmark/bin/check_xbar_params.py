#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Prove leg B1's HDL wrapper is the crossbar Vivado's IP catalog would build.

The sim and the OOC build instantiate axi_crossbar_v2_1 straight from the
Vivado install through rtl/generated/fb_data_fabric_xbar/fb_data_fabric.sv,
with parameters gen_fabric_legs.py computes. fpga/tcl/vendor_ip.tcl customizes
the same crossbar through the IP catalog (fb_xbar) from the same TOML. This
compares every C_* parameter the IP's generated top passes to the core against
the wrapper's, as integers, and exits 1 on any difference -- so "the B1 leg is
Xilinx's crossbar configured as the IP GUI would configure it" is checked, not
assumed.

Parameters the wrapper does not pass take the core's default; the IP top sets
them explicitly (the USER widths, all 1 with C_AXI_SUPPORTS_USER_SIGNALS=0).
Those are compared against the core's declared defaults.
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

AREA = Path(__file__).resolve().parent.parent
WRAPPER = AREA / "rtl/generated/fb_data_fabric_xbar/fb_data_fabric.sv"
IP_TOP = AREA / "fpga/ip/build/fb_vendor_ip.gen/sources_1/ip/fb_xbar/synth/fb_xbar.v"
CORE = "axi_crossbar_v2_1/hdl/axi_crossbar_v2_1_vl_rfs.v"
CORE_MODULE = "axi_crossbar_v2_1_37_axi_crossbar"

PARAM = re.compile(r"\.(C_[A-Z0-9_]+)\s*\(\s*(.+?)\s*\)\s*,?\s*$")
DEFAULT = re.compile(r"parameter\s+(?:integer\s+|\[[^\]]*\]\s*)?(C_[A-Z0-9_]+)\s*=\s*([^,]+?)\s*(?:,|$)")


def value(text: str) -> int | str:
    """A Verilog literal as an int; a string literal as itself."""
    t = text.strip().replace("_", "")
    if t.startswith('"'):
        return t.strip('"')
    m = re.fullmatch(r"(\d+)?'([hHdDbB])([0-9a-fA-F]+)", t)
    if m:
        return int(m.group(3), {"h": 16, "d": 10, "b": 2}[m.group(2).lower()])
    return int(t, 0)


def fmt(v: int | str) -> str:
    return f"0x{v:X}" if isinstance(v, int) and v > 255 else repr(v)


def params(path: Path) -> dict[str, int | str]:
    out = {}
    for line in path.read_text().splitlines():
        m = PARAM.search(line)
        if m:
            out[m.group(1)] = value(m.group(2))
    return out


def core_defaults(core: Path) -> dict[str, int | str]:
    text = core.read_text(errors="replace")
    start = text.index(f"module {CORE_MODULE}")
    header = text[start:text.index(");", start)]
    out = {}
    for m in DEFAULT.finditer(header):
        try:
            out[m.group(1)] = value(m.group(2))
        except ValueError:
            pass
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--ip-top", type=Path, default=IP_TOP)
    ap.add_argument("--wrapper", type=Path, default=WRAPPER)
    args = ap.parse_args()
    if not args.ip_top.exists():
        print(f"check_xbar_params: {args.ip_top} missing -- run fpga/tcl/vendor_ip.tcl first")
        return 1
    vivado = os.environ.get("XILINX_VIVADO")
    if not vivado:
        print("check_xbar_params: XILINX_VIVADO is not set (the core's defaults live there)")
        return 1
    ip, wrapper = params(args.ip_top), params(args.wrapper)
    defaults = core_defaults(Path(vivado) / "data/ip/xilinx" / CORE)
    diffs, by_default = [], []
    for name, want in sorted(ip.items()):
        if name in wrapper:
            got = wrapper[name]
        elif name in defaults:
            got = defaults[name]
            by_default.append(name)
        else:
            diffs.append(f"{name}: IP passes {want!r}, wrapper does not and no core default found")
            continue
        if got != want:
            diffs.append(f"{name}: IP {fmt(want)}  wrapper {fmt(got)}")
    extra = sorted(set(wrapper) - set(ip))
    for name in extra:
        diffs.append(f"{name}: wrapper passes it, the IP top does not")
    print(f"check_xbar_params: {len(ip)} IP parameters compared "
          f"({len(ip) - len(by_default)} against the wrapper, {len(by_default)} against core "
          f"defaults: {', '.join(by_default) or '-'})")
    for d in diffs:
        print(f"  MISMATCH {d}")
    print("check_xbar_params: " + ("FAIL" if diffs else "PASS -- leg B1 wrapper == IP-catalog crossbar"))
    return 1 if diffs else 0


if __name__ == "__main__":
    sys.exit(main())
