#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""elaborate_a7ddrphy.py -- generate the REAL LiteDRAM a7ddrphy as standalone Verilog.

Emits `a7ddrphy_generated.v`: A7DDRPHY (Artix-7, DDR2, 4:1 / nphases=4) with
  * its DFI 4-phase interface exposed as top-level ports (driven by OUR controller
    via the dfi_v21_flat_to_a7ddrphy adapter),
  * its calibration CSRs routed onto a 32-bit CSR bus (adr/we/dat_w/dat_r) so the
    UART/firmware host can run read/write leveling -- NO leveling FSM (per direction:
    FSMs breed bugs; firmware drives the knobs),
  * the ddram pads (verified Nexys A7 pinout, banks 34/35),
  * sys / sys2x / sys4x / sys4x_dqs clock inputs (harness MMCM drives these;
    IDELAYCTRL + the 90-deg sys4x_dqs live in the harness CRG).

Run inside the litex venv:
    source /tmp/litex-venv/bin/activate
    python3 elaborate_a7ddrphy.py --out <dir>/a7ddrphy_generated.v
"""

import argparse
import sys

from migen import Module, ClockDomain
from migen.fhdl import verilog

from litex.build.generic_platform import Pins, Subsignal, IOStandard, Misc
from litex.build.xilinx import XilinxPlatform
from litex.soc.interconnect import csr_bus

from litedram.phy.s7ddrphy import A7DDRPHY

# Verified Nexys A7 (== Nexys4 DDR) DDR2 pinout -- authoritative source:
# litex-boards litex_boards/platforms/digilent_nexys4ddr.py.  MT47H64M16HR-25E,
# 13 address bits, x16, banks 34/35, SSTL18_II / DIFF_SSTL18_II.
_io = [
    ("clk100", 0, Pins("E3"), IOStandard("LVCMOS33")),  # board 100 MHz (unused here, keeps platform happy)
    ("ddram", 0,
        Subsignal("a", Pins(
            "M4 P4 M6 T1 L3 P5 M2 N1",
            "L4 N5 R2 K5 N6"),
            IOStandard("SSTL18_II")),
        Subsignal("ba",    Pins("P2 P3 R1"), IOStandard("SSTL18_II")),
        Subsignal("ras_n", Pins("N4"), IOStandard("SSTL18_II")),
        Subsignal("cas_n", Pins("L1"), IOStandard("SSTL18_II")),
        Subsignal("we_n",  Pins("N2"), IOStandard("SSTL18_II")),
        Subsignal("dm", Pins("T6 U1"), IOStandard("SSTL18_II")),
        Subsignal("dq", Pins(
            "R7 V6 R8 U7 V7 R6 U6 R5",
            "T5 U3 V5 U4 V4 T4 V1 T3"),
            IOStandard("SSTL18_II"),
            Misc("IN_TERM=UNTUNED_SPLIT_50")),
        Subsignal("dqs_p", Pins("U9 U2"), IOStandard("DIFF_SSTL18_II")),
        Subsignal("dqs_n", Pins("V9 V2"), IOStandard("DIFF_SSTL18_II")),
        Subsignal("clk_p", Pins("L6"), IOStandard("DIFF_SSTL18_II")),
        Subsignal("clk_n", Pins("L5"), IOStandard("DIFF_SSTL18_II")),
        Subsignal("cke",   Pins("M1"), IOStandard("SSTL18_II")),
        Subsignal("odt",   Pins("M3"), IOStandard("SSTL18_II")),
        Subsignal("cs_n",  Pins("K6"), IOStandard("SSTL18_II")),
        Misc("SLEW=FAST"),
    ),
]


class NexysA7Platform(XilinxPlatform):
    default_clk_name = "clk100"

    def __init__(self):
        XilinxPlatform.__init__(self, "xc7a100tcsg324-1", _io, toolchain="vivado")


class A7DDRPHYStandalone(Module):
    """A7DDRPHY with DFI + CSR bus + clocks + pads broken out as top-level ports."""

    def __init__(self, platform):
        pads = platform.request("ddram")

        # Clock domains the PHY consumes -- driven by top-level input clocks.
        self.clock_domains.cd_sys       = ClockDomain("sys")
        self.clock_domains.cd_sys2x     = ClockDomain("sys2x")
        self.clock_domains.cd_sys4x     = ClockDomain("sys4x")
        self.clock_domains.cd_sys4x_dqs = ClockDomain("sys4x_dqs")

        self.submodules.phy = phy = A7DDRPHY(
            pads,
            memtype          = "DDR2",
            sys_clk_freq     = 100e6,
            iodelay_clk_freq = 200e6,
        )

        # Route the PHY calibration CSRs onto a 32-bit CSR bus (host/UART writable).
        csrs = phy.get_csrs()
        self.submodules.csrbank = bank = csr_bus.CSRBank(
            csrs, bus=csr_bus.Interface(data_width=32, address_width=10))

        # Handles for the io-collection step.
        self._pads   = pads
        self._dfi    = phy.dfi
        self._csrbus = bank.bus


def collect_ios(top):
    ios = set()
    for cd in (top.cd_sys, top.cd_sys2x, top.cd_sys4x, top.cd_sys4x_dqs):
        ios.add(cd.clk)
        ios.add(cd.rst)
    ios |= set(top._dfi.flatten())
    ios |= {top._csrbus.adr, top._csrbus.we, top._csrbus.dat_w, top._csrbus.dat_r}
    ios |= set(top._pads.flatten())
    return ios


def dump_csr_map(top, path=None):
    """Emit the calibration CSR bus map (word offset -> register) for firmware.

    32-bit CSR bus: byte offset = word_index * 4. These are the read/write
    leveling knobs the UART/firmware host drives (no leveling FSM in HW).
    """
    lines = ["# a7ddrphy calibration CSR map (32-bit bus; byte_off = word*4)",
             "# word  byte_off  name                  bits  kind"]
    kinds = {  # storage = persistent config; strobe = write-1-to-pulse
        "rst": "storage", "dly_sel": "storage", "half_sys8x_taps": "storage",
        "wlevel_en": "storage", "rdphase": "storage", "wrphase": "storage",
    }
    for i, c in enumerate(top.csrbank.simple_csrs):
        base = c.name.rstrip("0123456789") if c.name[-1].isdigit() else c.name
        kind = kinds.get(base, "strobe")
        lines.append(f"# {i:>4}  0x{i*4:04x}    {c.name:<20}  {c.size:>3}   {kind}")
    text = "\n".join(lines) + "\n"
    print(text, end="")
    if path:
        with open(path, "w") as f:
            f.write(text)
        print(f"wrote {path}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="a7ddrphy_generated.v")
    ap.add_argument("--dump-csr-map", action="store_true",
                    help="print the calibration CSR bus map and exit")
    ap.add_argument("--csr-map-out", default=None,
                    help="also write the CSR map to this file")
    args = ap.parse_args()

    platform = NexysA7Platform()
    top = A7DDRPHYStandalone(platform)

    if args.dump_csr_map or args.csr_map_out:
        dump_csr_map(top, args.csr_map_out)
        if args.dump_csr_map:
            return 0

    ios = collect_ios(top)
    out = verilog.convert(top, ios=ios, name="a7ddrphy")
    out.write(args.out)
    print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
