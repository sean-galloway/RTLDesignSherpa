# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: SyncPulseTB
# Purpose: Testbench for sync_pulse
# Subsystem: framework
#
# sync_pulse had NO simulation test at all until 2026-08-07, despite being
# LIVE: projects/NexysA7/cdc_counter_display/rtl/cdc_counter_domain.sv
# instantiates it three times (u_load_sync, u_host_press_sync, u_alive_sync)
# to carry pulses between the system and counter clock domains. It also has a
# formal harness (formal/cdc/sync_pulse).
#
# CORRECTION (2026-08-08): this header first said the module had "no
# instantiations anywhere in the tree". That was wrong -- the grep behind it
# searched rtl/ only and never looked in projects/. A board design depends on
# this synchroniser.

import os
import random

import cocotb
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase


class SyncPulseTB(TBBase):
    """Testbench for sync_pulse: a toggle-based CDC pulse synchronizer.

    The DUT toggles a flop in the source domain on every `i_pulse`, carries the
    toggle across an N-deep synchronizer in the destination domain, and edge
    detects it -- so ONE source pulse must produce exactly ONE destination
    pulse, one destination clock wide, however the two clocks are related.

    The checks are all conservation properties, which is what makes them worth
    asserting: pulses in equals pulses out, no output while the input is idle,
    and nothing emitted out of reset.
    """

    LEVELS = {'gate': 1, 'func': 3, 'full': 10}

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)

        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in self.LEVELS:
            self.TEST_LEVEL = 'gate'
        self.LEVEL_MULT = self.LEVELS[self.TEST_LEVEL]

        self.SYNC_STAGES = self.convert_to_int(os.environ.get('PARAM_SYNC_STAGES', '3'))
        self.SRC_PERIOD = self.convert_to_int(os.environ.get('TEST_SRC_PERIOD', '10'))
        self.DST_PERIOD = self.convert_to_int(os.environ.get('TEST_DST_PERIOD', '10'))

        # 8 pulses at gate, 24 at func, 80 at full -- the depth knob drives real
        # work rather than sitting in a dict nothing reads.
        self.PULSES = 8 * self.LEVEL_MULT

        self.log.info(
            f"SyncPulseTB: SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}, "
            f"SYNC_STAGES={self.SYNC_STAGES}, src={self.SRC_PERIOD}ns, "
            f"dst={self.DST_PERIOD}ns, pulses={self.PULSES}")

        self._seen = 0          # destination pulses counted by the monitor
        self._widths_bad = []   # output pulses that were not exactly 1 dst clock

    # ---- contract lifecycle (/GLOBAL_REQUIREMENTS.md 2.2) ----------------

    async def assert_reset(self):
        """Assert both domain resets and idle the input."""
        self.dut.i_src_rst_n.value = 0
        self.dut.i_dst_rst_n.value = 0
        self.dut.i_pulse.value = 0

    async def deassert_reset(self):
        """Release both domain resets."""
        self.dut.i_src_rst_n.value = 1
        self.dut.i_dst_rst_n.value = 1

    async def setup_clocks_and_reset(self):
        """Start both clocks and drive the full reset sequence."""
        await self.start_clock('i_src_clk', self.SRC_PERIOD, 'ns')
        await self.start_clock('i_dst_clk', self.DST_PERIOD, 'ns')
        await self.assert_reset()
        await self.wait_clocks('i_dst_clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('i_dst_clk', 5)

    # ---- monitor ---------------------------------------------------------

    async def _watch_output(self):
        """Count destination pulses and check each is exactly one clock wide.

        Sampling goes through wait_clocks, which always lands clear of the
        edge -- reading o_pulse in the delta around a RisingEdge is how a
        combinational output gets misread as toggling.
        """
        run = 0
        while True:
            await self.wait_clocks('i_dst_clk', 1)
            val = self.dut.o_pulse.value
            hi = val.is_resolvable and int(val) == 1
            if hi:
                run += 1
            elif run:
                self._seen += 1
                if run != 1:
                    self._widths_bad.append(run)
                run = 0

    # ---- stimulus --------------------------------------------------------

    async def send_pulse(self):
        """One source-domain pulse, one source clock wide."""
        await self.wait_clocks('i_src_clk', 1)
        self.dut.i_pulse.value = 1
        await self.wait_clocks('i_src_clk', 1)
        self.dut.i_pulse.value = 0

    def _settle_cycles(self):
        """Destination cycles needed for one pulse to propagate and be seen.

        SYNC_STAGES flops plus the edge-detect flop, plus slack for the source
        period when the source is the slower clock.
        """
        ratio = max(1, (self.SRC_PERIOD + self.DST_PERIOD - 1) // self.DST_PERIOD)
        return self.SYNC_STAGES + 2 + 2 * ratio

    async def run_test(self):
        """Drive PULSES source pulses and assert one destination pulse each."""
        cocotb.start_soon(self._watch_output())

        # Nothing may be emitted while the input is idle.
        await self.wait_clocks('i_dst_clk', self._settle_cycles() + 5)
        assert self._seen == 0, (
            f"{self._seen} destination pulse(s) emitted with i_pulse held low "
            f"since reset -- the synchronizer invented an edge")

        for i in range(self.PULSES):
            await self.send_pulse()
            # Space pulses so each is independently observable. Back-to-back
            # toggling is a different property and is not what this checks.
            gap = self._settle_cycles() + random.randint(0, 3)
            await self.wait_clocks('i_dst_clk', gap)
            assert self._seen == i + 1, (
                f"after {i + 1} source pulse(s) the destination saw "
                f"{self._seen}; a toggle synchronizer must deliver exactly one "
                f"pulse per source pulse (SYNC_STAGES={self.SYNC_STAGES}, "
                f"src={self.SRC_PERIOD}ns, dst={self.DST_PERIOD}ns)")

        await self.wait_clocks('i_dst_clk', self._settle_cycles() + 5)

        assert self._seen == self.PULSES, (
            f"sent {self.PULSES} source pulses, destination saw {self._seen}")
        assert not self._widths_bad, (
            f"destination pulse(s) not one clock wide: widths {self._widths_bad}")

        # And the line goes quiet again once the input does.
        quiet = self._seen
        await self.wait_clocks('i_dst_clk', 20)
        assert self._seen == quiet, (
            f"{self._seen - quiet} extra destination pulse(s) after the source "
            f"went idle")

        self.log.info(
            f"sync_pulse: {self.PULSES} pulses delivered 1:1 across "
            f"{self.SRC_PERIOD}ns -> {self.DST_PERIOD}ns, all one clock wide")

    async def run_reset_mid_stream(self):
        """A destination-domain reset must not emit a pulse by itself."""
        before = self._seen
        self.dut.i_dst_rst_n.value = 0
        await self.wait_clocks('i_dst_clk', 4)
        self.dut.i_dst_rst_n.value = 1
        await self.wait_clocks('i_dst_clk', self._settle_cycles() + 5)
        assert self._seen == before, (
            f"destination reset emitted {self._seen - before} spurious "
            f"pulse(s); r_sync and r_sync_prev must clear together so the "
            f"edge detector sees no transition")
        self.log.info("sync_pulse: destination reset emitted no spurious pulse")
