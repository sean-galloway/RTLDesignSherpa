#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Authored-once host PROGRAMS for the CDC counter demo.

These functions take a `CdcDemoDriver` and drive the harness by name. They are
pure logic (no printing, no argparse) so the *identical* program runs against
the FPGA (from run_cdc_demo.py over pyserial) and in a cocotb sim (from
dv/tests/test_cdc_demo_uart.py via cocotb.external over the real uart_axil_bridge
RTL). Same bytes on the wire → silicon and sim are equivalent.

The digital-contract programs (smoke / press / cfg_load / cdc_mode_check) return
result dataclasses the sim asserts on. `watch_fail` is the CLI-only headline
demo (its "garbage read" is an analog/timing effect that isn't asserted in sim).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Tuple

import cdc_demo as cd


# =============================================================================
# smoke — link + per-counter snapshot
# =============================================================================
@dataclass(frozen=True)
class CounterSnap:
    idx: int
    divisor: int
    init: int
    increment: int
    value: int
    press_count: int
    cdc_mode: int
    auto_inc: int


@dataclass(frozen=True)
class SmokeResult:
    build_id: int
    build_id_ok: bool
    scratch: List[Tuple[int, int, bool]] = field(default_factory=list)  # (wrote, read, ok)
    counters: List[CounterSnap] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return self.build_id_ok and all(o for _w, _r, o in self.scratch)


def smoke(drv: "cd.CdcDemoDriver") -> SmokeResult:
    bid = drv.build_id()
    scratch = []
    for v in (0xDEAD_BEEF, 0x1234_5678, 0xA5A5_5A5A):
        rb = drv.scratch(v)
        scratch.append((v, rb, rb == v))
    counters = []
    for i in range(cd.NUM_COUNTERS):
        c = drv.counter(i)
        counters.append(CounterSnap(
            idx=i,
            divisor=c._regs.read(c._n("DIVISOR")),
            init=c._regs.read(c._n("INIT")) & 0xFFFF,
            increment=c._regs.read(c._n("INCREMENT")) & 0xFFFF,
            value=c.value(),
            press_count=c.press_count(),
            cdc_mode=c.cdc_mode(),
            auto_inc=c.auto_inc(),
        ))
    return SmokeResult(build_id=bid, build_id_ok=(bid == cd.EXPECTED_BUILD_ID),
                       scratch=scratch, counters=counters)


# =============================================================================
# press — inject N host presses, verify VALUE + PRESS_COUNT
# =============================================================================
@dataclass(frozen=True)
class PressResult:
    counter: int
    init: int
    increment: int
    count: int
    value_before: int
    value_after: int
    value_expected: int
    press_delta: int

    @property
    def ok(self) -> bool:
        return (self.value_after == self.value_expected
                and self.press_delta == self.count)


def press(drv: "cd.CdcDemoDriver", counter: int, count: int,
          *, init: int = 0x10, increment: int = 3,
          cdc_mode: int = cd.CDC_NO_CDC) -> PressResult:
    """Load INIT, inject `count` HOST_PRESS pulses, check VALUE / PRESS_COUNT.

    Uses NO_CDC readback by default: in the digital sim (and after settle on
    silicon) the raw value path reflects the true counter, so VALUE is exact.
    """
    c = drv.counter(counter)
    c.set_cdc_mode(cdc_mode)
    c.set_auto_inc(0)
    c.set_init(init)
    c.set_increment(increment)
    c.load()

    value_before = c.value()
    pc_before = c.press_count()
    for _ in range(count):
        c.press()
    value_after = c.value()
    pc_after = c.press_count()

    return PressResult(
        counter=counter, init=init, increment=increment, count=count,
        value_before=value_before, value_after=value_after,
        value_expected=(init + count * increment) & 0xFFFF,
        press_delta=(pc_after - pc_before) & 0xFFFF)


# =============================================================================
# cfg_load — CFG_LOAD reloads VALUE to INIT without disturbing PRESS_COUNT
# =============================================================================
@dataclass(frozen=True)
class CfgLoadResult:
    counter: int
    value_mid: int
    press_mid: int
    value_reload: int
    press_reload: int
    reload_target: int

    @property
    def ok(self) -> bool:
        return (self.value_reload == self.reload_target
                and self.press_reload == self.press_mid)


def cfg_load(drv: "cd.CdcDemoDriver", counter: int,
             *, cdc_mode: int = cd.CDC_NO_CDC) -> CfgLoadResult:
    c = drv.counter(counter)
    c.set_cdc_mode(cdc_mode)
    c.set_auto_inc(0)
    c.set_init(0x0000)
    c.set_increment(1)
    c.load()

    for _ in range(5):
        c.press()
    value_mid = c.value()
    press_mid = c.press_count()

    # Reload to a distinct value; PRESS_COUNT must be untouched.
    reload_target = 0xBEEF
    c.set_init(reload_target)
    c.load()
    return CfgLoadResult(counter=counter, value_mid=value_mid, press_mid=press_mid,
                         value_reload=c.value(), press_reload=c.press_count(),
                         reload_target=reload_target)


# =============================================================================
# cdc_mode_check — every CDC_MODE code round-trips through the CSR
# =============================================================================
@dataclass(frozen=True)
class CdcModeResult:
    counter: int
    checks: List[Tuple[int, int]] = field(default_factory=list)  # (wrote, read)

    @property
    def ok(self) -> bool:
        return all(w == r for w, r in self.checks)


def cdc_mode_check(drv: "cd.CdcDemoDriver", counter: int) -> CdcModeResult:
    c = drv.counter(counter)
    checks = []
    for mode in (cd.CDC_NO_CDC, cd.CDC_STRETCH, cd.CDC_SYNC_FIFO,
                 cd.CDC_TWO_PHASE, cd.CDC_FOUR_PHASE):
        c.set_cdc_mode(mode)
        checks.append((mode, c.cdc_mode()))
    c.set_cdc_mode(cd.CDC_NO_CDC)   # leave it in the default
    return CdcModeResult(counter=counter, checks=checks)


# =============================================================================
# watch_fail — CLI-only headline demo (NOT asserted in sim)
# =============================================================================
@dataclass
class WatchFailRow:
    pickoff: int
    f_ctr_hz: float
    samples: List[int]

    @property
    def unique(self) -> int:
        return len(set(self.samples))

    @property
    def spread(self) -> int:
        return (max(self.samples) - min(self.samples)) & 0xFF


def watch_fail(drv: "cd.CdcDemoDriver", counter: int,
               pickoffs: List[int], *, samples_per: int = 10,
               sample_delay_s: float = 0.05,
               settle_s: float = 0.1) -> List[WatchFailRow]:
    """Put one counter in NO-CDC + AUTO_INC, sweep pickoff slow→fast, sample
    VALUE. Wide spread at fast clocks = broken multi-bit crossing (silicon)."""
    import time
    c = drv.counter(counter)
    drv.disp_select(counter)
    c.set_cdc_mode(cd.CDC_NO_CDC)
    c.set_auto_inc(1)
    c.set_init(0)
    c.set_increment(1)
    c.load()
    time.sleep(2 * settle_s)

    rows: List[WatchFailRow] = []
    for po in pickoffs:
        c.set_div_pickoff(po)
        time.sleep(settle_s)
        samples = []
        for _ in range(samples_per):
            samples.append(c.value())
            time.sleep(sample_delay_s)
        rows.append(WatchFailRow(pickoff=po,
                                 f_ctr_hz=cd.CLK_HZ / (1 << (po + 1)),
                                 samples=samples))
    # Leave the display counter in a clean state.
    c.set_cdc_mode(cd.CDC_SYNC_FIFO)
    c.set_auto_inc(0)
    c.set_div_pickoff(23)
    return rows
