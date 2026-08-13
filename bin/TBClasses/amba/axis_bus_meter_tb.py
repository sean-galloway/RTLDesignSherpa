# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: AxisBusMeterTB
# Purpose: Testbench for axis_bus_meter (rtl/amba/shared/axis_bus_meter.sv)
# Subsystem: framework
#
# Same rationale as AxiBusMeterTB (bin/TBClasses/amba/axi_bus_meter_tb.py):
# axis_bus_meter is a pure passive observer of bare tvalid/tready/tlast/
# tstrb/tid taps, not a framed AXIS transfer with a real producer/consumer
# behind it -- there is no sequence for an AXIS BFM to run, and GAXI would be
# driving/checking a data-carrying skid interface the module doesn't have.
# Directed per-cycle stimulus plus a software mirror of the RTL's four-bucket
# classification (identical to axi_bus_meter) plus the AXIS-native byte/
# packet counters is the correct tool.

import os
import random

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase

# Bucket -> overflow-sticky bit position. Matches r_ch_overflow packing
# {prod, bp, starv, idle} in axis_bus_meter.sv (o_ch_overflow[c*4 +: 4]).
OVERFLOW_BIT = {'productive': 3, 'backpressure': 2, 'starvation': 1, 'idle': 0}
CH_COUNTER_MASK = 0xFFFF


def classify(tvalid: int, tready: int) -> str:
    """Software mirror of axis_bus_meter's combinational bucket decode."""
    if tvalid and tready:
        return 'productive'
    if tvalid and not tready:
        return 'backpressure'
    if not tvalid and tready:
        return 'starvation'
    return 'idle'


def popcount(x: int) -> int:
    return bin(x).count('1')


class AxisBusMeterTB(TBBase):
    def __init__(self, dut, num_channels: int = 4, sw: int = 4):
        super().__init__(dut)
        self.dut = dut
        # NUM_CHANNELS must be a power of 2: the RTL bins by
        # i_tid[CW-1:0] (a bit mask), not tid % NUM_CHANNELS -- a
        # non-power-of-2 channel count would let w_ch alias out of range.
        assert (num_channels & (num_channels - 1)) == 0, \
            "AxisBusMeterTB requires a power-of-2 NUM_CHANNELS (RTL bins by tid bit mask)"
        self.NUM_CHANNELS = num_channels
        self.SW = sw  # tstrb width = DATA_WIDTH / 8
        self.SEED = int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)
        self.reset_mirror()

    def reset_mirror(self):
        self.agg = {'productive': 0, 'backpressure': 0, 'starvation': 0, 'idle': 0}
        self.agg_bytes = 0
        self.agg_beats = 0
        self.agg_packets = 0
        # Per-channel idle is structurally unreachable in this RTL (no tid is
        # meaningful with nothing on the bus) -- kept in the mirror purely so
        # assert_ch_matches can pin o_ch_idle at 0 for every channel.
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
        self.dut.i_tvalid.value = 0
        self.dut.i_tready.value = 0
        self.dut.i_tlast.value = 0
        self.dut.i_tstrb.value = 0
        self.dut.i_tid.value = 0
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 2)
        # Same reasoning as AxiBusMeterTB.setup_clocks_and_reset: the idle
        # cycles above count in hardware, so sync mirror-zero and DUT-zero
        # via a real i_clear pulse rather than assuming they line up.
        await self.clear_pulse()

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # ------------------------------------------------------------------
    # Stimulus
    # ------------------------------------------------------------------
    async def drive_cycle(self, tvalid: int, tready: int, tid: int = 0,
                           tlast: int = 0, tstrb=None, freeze: int = 0):
        """Drive one snoop cycle and update the software mirror to match
        what the RTL registers on THIS clock edge."""
        if tstrb is None:
            tstrb = (1 << self.SW) - 1  # all-ones default (doc recommendation)
        self.dut.i_tvalid.value = tvalid
        self.dut.i_tready.value = tready
        self.dut.i_tid.value = tid
        self.dut.i_tlast.value = tlast
        self.dut.i_tstrb.value = tstrb
        self.dut.i_freeze.value = freeze
        self.dut.i_clear.value = 0

        if not freeze:
            bucket = classify(tvalid, tready)
            self.agg[bucket] += 1
            ch = tid & (self.NUM_CHANNELS - 1)
            # Per-channel binning attributes productive/backpressure/
            # starvation, but never idle (no if(w_idle) branch in the RTL).
            if bucket != 'idle':
                cnt = self.ch[ch][bucket]
                if cnt == CH_COUNTER_MASK:
                    self.ch_overflow[ch] |= (1 << OVERFLOW_BIT[bucket])
                self.ch[ch][bucket] = (cnt + 1) & CH_COUNTER_MASK
            if bucket == 'productive':
                self.agg_bytes += popcount(tstrb & ((1 << self.SW) - 1))
                self.agg_beats += 1
                if tlast:
                    self.agg_packets += 1
        await RisingEdge(self.dut.aclk)

    async def clear_pulse(self):
        """Synchronous one-cycle i_clear pulse: on this edge every counter
        and sticky zeroes, regardless of tvalid/tready/freeze."""
        self.dut.i_clear.value = 1
        self.dut.i_tvalid.value = 0
        self.dut.i_tready.value = 0
        self.dut.i_tlast.value = 0
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

    def read_throughput(self):
        return {
            'bytes':   int(self.dut.o_agg_bytes.value),
            'beats':   int(self.dut.o_agg_beats.value),
            'packets': int(self.dut.o_agg_packets.value),
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

    def assert_throughput_matches(self, label: str = ""):
        got = self.read_throughput()
        want = {'bytes': self.agg_bytes, 'beats': self.agg_beats,
                'packets': self.agg_packets}
        assert got == want, f"{label}: throughput mismatch got={got} want={want}"

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
