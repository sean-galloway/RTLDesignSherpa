#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host-side driver for the CDC counter demo harness (cdc_demo_top / cdc_demo_harness).

Wraps `UARTAxiBridge` (projects/components/converters/bin) with by-name register
access via `UartRegisterMap`, backed by the PeakRDL-generated
`cdc_demo_csr_regmap.py`. NO hardcoded offsets — the register layout is
authoritative in `rtl/cdc_demo_harness.sv`, described in `rtl/cdc_demo_csr.rdl`,
and a consistency test guards drift.

Because the bridge is INJECTABLE, the identical driver drives the FPGA over
pyserial *or* a cocotb sim over `CocotbUartChannel` — silicon and sim are
byte-for-byte equivalent at the UART wire.

    from cdc_demo import CdcDemoDriver, EXPECTED_BUILD_ID

    d = CdcDemoDriver(port="/dev/ttyUSB1")          # FPGA
    assert d.build_id() == EXPECTED_BUILD_ID
    c2 = d.counter(2)
    c2.set_cdc_mode(2); c2.set_init(0x10); c2.set_increment(3); c2.load()
    c2.press(); print(hex(c2.value()), c2.press_count())

    # sim: d = CdcDemoDriver(bridge=UARTAxiBridge(channel=cocotb_channel))
"""

from __future__ import annotations

import os
import sys
from typing import Optional

# Shared UART client + by-name register map (both on PYTHONPATH via env_python).
_REPO_ROOT = os.environ.get("REPO_ROOT")
if not _REPO_ROOT:
    raise RuntimeError(
        "REPO_ROOT is not set. Source RTLDesignSherpa/env_python before "
        "importing cdc_demo.")
sys.path.insert(0, os.path.join(_REPO_ROOT, "projects/components/converters/bin"))
from uart_axi_bridge import UARTAxiBridge                          # noqa: E402
from TBClasses.harness.uart_register_map import UartRegisterMap    # noqa: E402

# cdc_demo_harness is a single flat AXIL slave — harness base = 0x0.
HARNESS_BASE = 0x0

# PeakRDL-generated regmap for cdc_demo_csr (by-name access).
CDC_REGMAP = os.path.join(
    _REPO_ROOT, "projects/NexysA7/cdc_counter_display/dv/tbclasses/"
    "cdc_demo_csr_regmap.py")

EXPECTED_BUILD_ID = 0x4344_4331   # "CDC1"
NUM_COUNTERS      = 4
CLK_HZ            = 100_000_000   # sys_clk

# CDC_MODE encodings (mirror cdc_counter_domain.sv).
CDC_NO_CDC     = 0
CDC_STRETCH    = 1
CDC_SYNC_FIFO  = 2
CDC_TWO_PHASE  = 3
CDC_FOUR_PHASE = 4

CDC_MODE_NAMES = {
    CDC_NO_CDC:     "NO-CDC",
    CDC_STRETCH:    "STRETCH (cdc_open_loop, ~20 MHz cliff)",
    CDC_SYNC_FIFO:  "SYNC-FIFO (fifo_async)",
    CDC_TWO_PHASE:  "TWO-PHASE (cdc_2_phase_handshake)",
    CDC_FOUR_PHASE: "FOUR-PHASE (cdc_4_phase_handshake)",
}

# DIVISOR field: clock_select=4 selects the sys_clk-derived divided clock; the
# 5-bit div_pickoff then sets ctr_clk = sys_clk / 2^(pickoff+1).
CLOCK_SELECT_DIVIDED = 4


class Counter:
    """By-name accessor for one per-counter block (regmap keys COUNTER{i}_*)."""

    def __init__(self, regs: UartRegisterMap, idx: int):
        if not 0 <= idx < NUM_COUNTERS:
            raise ValueError(f"counter index out of range: {idx}")
        self._regs = regs
        self.i = idx

    def _n(self, reg: str) -> str:
        return f"COUNTER{self.i}_{reg}"

    # ----- config writes ---------------------------------------------------
    def set_clock_select(self, sel: int) -> None:
        self._regs.write(self._n("DIVISOR"), rmw=True, clock_select=sel & 0x7)

    def set_div_pickoff(self, pickoff: int) -> None:
        """Select the divided clock at the given pickoff (clock_select=4)."""
        self._regs.write(self._n("DIVISOR"), rmw=True,
                         clock_select=CLOCK_SELECT_DIVIDED,
                         div_pickoff=pickoff & 0x1F)

    def set_divisor_raw(self, word: int) -> None:
        self._regs.write_word(self._n("DIVISOR"), word)

    def set_init(self, init: int) -> None:
        self._regs.write(self._n("INIT"), value=init & 0xFFFF)

    def set_increment(self, inc: int) -> None:
        self._regs.write(self._n("INCREMENT"), value=inc & 0xFFFF)

    def load(self) -> None:
        self._regs.write(self._n("CFG_LOAD"), strobe=1)

    def press(self) -> None:
        self._regs.write(self._n("HOST_PRESS"), strobe=1)

    def set_cdc_mode(self, mode: int) -> None:
        self._regs.write(self._n("CDC_MODE"), mode=mode & 0x7)

    def set_auto_inc(self, en: int) -> None:
        self._regs.write(self._n("AUTO_INC"), en=en & 1)

    # ----- status reads ----------------------------------------------------
    def value(self) -> int:
        return self._regs.read(self._n("VALUE")) & 0xFFFF

    def press_count(self) -> int:
        return self._regs.read(self._n("PRESS_COUNT")) & 0xFFFF

    def clk_ticks(self) -> int:
        return self._regs.read(self._n("CTR_CLK_TICKS")) & 0xFFFF_FFFF

    def cdc_mode(self) -> int:
        return self._regs.field(self._n("CDC_MODE"), "mode")

    def auto_inc(self) -> int:
        return self._regs.field(self._n("AUTO_INC"), "en")

    def clock_select(self) -> int:
        return self._regs.field(self._n("DIVISOR"), "clock_select")

    def div_pickoff(self) -> int:
        return self._regs.field(self._n("DIVISOR"), "div_pickoff")


class CdcDemoDriver:
    """Named-register driver for cdc_demo_harness over the UART/AXIL bridge.

    All access goes by name through `self.regs` (UartRegisterMap), sourced from
    the PeakRDL regmap. Inject `bridge=UARTAxiBridge(channel=...)` to drive a
    cocotb sim; otherwise a real UART bridge is opened on `port`.
    """

    def __init__(self, *, port: str = "/dev/ttyUSB1", baud: int = 115200,
                 timeout: float = 1.0, bridge=None,
                 regmap_file: str = CDC_REGMAP):
        self.bridge = bridge if bridge is not None else UARTAxiBridge(
            port=port, baudrate=baud, timeout=timeout)
        self.regs = UartRegisterMap(self.bridge, HARNESS_BASE, regmap_file)


def autodetect_port(baud: int = 115200, want: str = None) -> str:
    """Find the ttyUSB the cdc_demo harness is on.

    The USB-UART re-enumerates across reboots/replugs, so never hardcode the
    port. Probe each candidate by reading BUILD_ID; the board that answers with
    the 'CDC1' magic is ours. `want`: if the caller passed --port explicitly (not
    'auto'), try it first. Mirrors the STREAM/RAPIDS char autodetect with the cdc
    identity register."""
    import glob
    cands = []
    if want and want != "auto":
        cands.append(want)
    cands += sorted(p for p in glob.glob("/dev/ttyUSB*") if p not in cands)

    for port in cands:
        try:
            d = CdcDemoDriver(port=port, baud=baud, timeout=0.4)
            ok = d.build_id() == EXPECTED_BUILD_ID
            ser = getattr(d.bridge, "ser", None)
            if ser is not None:
                ser.close()
            if ok:
                print(f"[autodetect] cdc_demo harness found on {port}")
                return port
        except Exception:
            continue
    raise SystemExit(
        f"[autodetect] no cdc_demo harness responded on any of: "
        f"{cands or '(no /dev/ttyUSB* present)'}. "
        f"Is the board powered and programmed with the cdc_demo bitstream?")

    # ----- global registers ------------------------------------------------
    def build_id(self) -> int:
        return self.regs.read("BUILD_ID")

    def scratch(self, val: Optional[int] = None) -> int:
        """Write then read-back SCRATCH (round-trip) when `val` given; else read."""
        if val is not None:
            self.regs.write("SCRATCH", value=val)
        return self.regs.read("SCRATCH")

    def soft_reset(self) -> None:
        self.regs.write("CTRL", soft_reset=1)

    def disp_select(self, idx: Optional[int] = None) -> int:
        if idx is not None:
            self.regs.write("DISP_SELECT", sel=idx & 0x3)
        return self.regs.field("DISP_SELECT", "sel")

    def status(self) -> int:
        return self.regs.read("STATUS")

    def counter(self, idx: int) -> Counter:
        return Counter(self.regs, idx)

    # ----- lifecycle -------------------------------------------------------
    def close(self) -> None:
        chan = getattr(self.bridge, "ser", None)
        if chan is not None and hasattr(chan, "close"):
            chan.close()
