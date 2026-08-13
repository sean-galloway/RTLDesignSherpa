# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: AxiBusMeterTB
# Purpose: Testbench for axi_bus_meter (rtl/amba/shared/axi_bus_meter.sv)
# Subsystem: framework
#
# axi_bus_meter is a pure passive per-cycle valid/ready bucket counter fed
# from bare snoop taps (i_valid/i_ready/i_channel_id/i_channel_valid) -- there
# is no AR/AW/R/W/B channel to drive, no burst framing, no id-based response
# ordering. Per [[bfm-usage]] "custom valid/ready -> GAXI" is also the wrong
# fit here: GAXI drives/monitors a data-carrying skid interface, whereas this
# module's "payload" IS the valid/ready pair itself. Directed per-cycle
# stimulus plus a software mirror of the RTL's four-bucket classification is
# the correct tool -- the same choice the sibling axi_perf_latency_hist TB
# makes for its bare cmd/data/resp taps (see test_axi_perf_latency_hist.py).

import os
import random

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase

# Bucket -> overflow-sticky bit position. Matches r_ch_overflow packing
# {prod, bp, starv, idle} in axi_bus_meter.sv (o_ch_overflow[c*4 +: 4]).
OVERFLOW_BIT = {'productive': 3, 'backpressure': 2, 'starvation': 1, 'idle': 0}
CH_COUNTER_MASK = 0xFFFF


def classify(valid: int, ready: int) -> str:
    """Software mirror of axi_bus_meter's combinational bucket decode."""
    if valid and ready:
        return 'productive'
    if valid and not ready:
        return 'backpressure'
    if not valid and ready:
        return 'starvation'
    return 'idle'


class AxiBusMeterTB(TBBase):
    def __init__(self, dut, num_channels: int = 4):
        super().__init__(dut)
        self.dut = dut
        self.NUM_CHANNELS = num_channels
        self.SEED = int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)
        self.reset_mirror()

    def reset_mirror(self):
        self.agg = {'productive': 0, 'backpressure': 0, 'starvation': 0, 'idle': 0}
        self.ch = [
            {'productive': 0, 'backpressure': 0, 'starvation': 0, 'idle': 0}
            for _ in range(self.NUM_CHANNELS)
        ]
        self.ch_overflow = [0] * self.NUM_CHANNELS

    # ------------------------------------------------------------------
    # Mandatory three methods
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', 10, 'ns')
        self.dut.i_clear.value = 0
        self.dut.i_freeze.value = 0
        self.dut.i_valid.value = 0
        self.dut.i_ready.value = 0
        self.dut.i_channel_id.value = 0
        self.dut.i_channel_valid.value = 0
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 2)
        # The idle cycles above (i_valid=i_ready=0 while waiting out reset
        # recovery) DO count in hardware -- axi_bus_meter has no reset-vs-
        # measurement gate other than i_clear/i_freeze. Pulse i_clear here
        # so the mirror's zero state and the DUT's zero state are the same
        # cycle, rather than silently drifting by the wait_clocks count.
        await self.clear_pulse()

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # ------------------------------------------------------------------
    # Stimulus
    # ------------------------------------------------------------------
    async def drive_cycle(self, valid: int, ready: int, ch_id: int = 0,
                           ch_valid: int = 0, freeze: int = 0):
        """Drive one snoop cycle and update the software mirror to match
        what the RTL registers on THIS clock edge (reset > clear > freeze >
        normal, matching the RTL's if/else-if priority -- clear is handled
        by clear_pulse(), not here)."""
        self.dut.i_valid.value = valid
        self.dut.i_ready.value = ready
        self.dut.i_channel_id.value = ch_id
        self.dut.i_channel_valid.value = ch_valid
        self.dut.i_freeze.value = freeze
        self.dut.i_clear.value = 0

        if not freeze:
            bucket = classify(valid, ready)
            self.agg[bucket] += 1
            if ch_valid:
                cnt = self.ch[ch_id][bucket]
                if cnt == CH_COUNTER_MASK:
                    self.ch_overflow[ch_id] |= (1 << OVERFLOW_BIT[bucket])
                self.ch[ch_id][bucket] = (cnt + 1) & CH_COUNTER_MASK
        await RisingEdge(self.dut.aclk)

    async def clear_pulse(self):
        """Synchronous one-cycle i_clear pulse: on this edge every counter
        and sticky zeroes, regardless of valid/ready/freeze."""
        self.dut.i_clear.value = 1
        self.dut.i_valid.value = 0
        self.dut.i_ready.value = 0
        self.dut.i_channel_valid.value = 0
        await RisingEdge(self.dut.aclk)
        self.dut.i_clear.value = 0
        self.reset_mirror()

    async def settle(self):
        await Timer(1, 'ns')

    # ------------------------------------------------------------------
    # Readback + assertions
    # ------------------------------------------------------------------
    def read_agg(self):
        return {
            'productive':   int(self.dut.o_agg_productive.value),
            'backpressure': int(self.dut.o_agg_backpressure.value),
            'starvation':   int(self.dut.o_agg_starvation.value),
            'idle':         int(self.dut.o_agg_idle.value),
        }

    def read_ch(self, idx: int):
        return {
            'productive':   int(self.dut.o_ch_productive[idx].value),
            'backpressure': int(self.dut.o_ch_backpressure[idx].value),
            'starvation':   int(self.dut.o_ch_starvation[idx].value),
            'idle':         int(self.dut.o_ch_idle[idx].value),
        }

    def read_ch_overflow(self, idx: int) -> int:
        packed = int(self.dut.o_ch_overflow.value)
        return (packed >> (idx * 4)) & 0xF

    def assert_agg_matches(self, label: str = ""):
        got = self.read_agg()
        assert got == self.agg, f"{label}: agg mismatch got={got} want={self.agg}"

    def assert_ch_matches(self, idx: int, label: str = ""):
        got = self.read_ch(idx)
        assert got == self.ch[idx], (
            f"{label}: ch[{idx}] mismatch got={got} want={self.ch[idx]}"
        )
        got_ovf = self.read_ch_overflow(idx)
        assert got_ovf == self.ch_overflow[idx], (
            f"{label}: ch[{idx}] overflow got=0x{got_ovf:X} "
            f"want=0x{self.ch_overflow[idx]:X}"
        )

    def assert_all_ch_match(self, label: str = ""):
        for idx in range(self.NUM_CHANNELS):
            self.assert_ch_matches(idx, label)
