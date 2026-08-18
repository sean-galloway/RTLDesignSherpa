# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: Axis4PatternPairTB
# Purpose: Testbench for axis4_master_pattern_gen -> axis4_slave_pattern_check
# Subsystem: framework
#
# TB class lives here per rtl/amba/CLAUDE.md Rule #0 and GLOBAL_REQUIREMENTS
# 2.1/2.3; val/amba/test_axis4_pattern_pair.py holds only the parameter grid
# and the cocotb_test.run() call ([[tb-structure]]).

import os
import random

import cocotb
from cocotb.triggers import RisingEdge
from cocotb.utils import get_sim_time

from TBClasses.shared.tbbase import TBBase


class Axis4PatternPairTB(TBBase):
    """Closed loop: pattern generator into pattern checker.

    Both DUTs had zero coverage. The pair harness
    (`val/amba/tb_axis4_pattern_pair.sv`) already existed and was never
    wired to a test.

    They are a matched pair by construction — the generator streams
    LFSR data and accumulates an expected CRC per channel, the checker
    consumes it and accumulates an actual CRC per channel — so the
    meaningful assertion is CRC *agreement*, not merely that the
    checker reported no error. A checker that never sees data also
    reports no error, so every run first proves beats actually flowed.

    Two hardware details this TB has to respect, both learned by
    reading the RTL rather than guessing:

    * `cfg_start` on **both** blocks is a one-cycle pulse ("arm +
      seed"), not a level. The checker derives `w_load` straight from
      it, and `w_load` re-seeds its LFSRs and zeroes its beat counters.
      Hold it high and the generator streams happily while the checker
      reports nothing.
    * `cfg_done` on the generator is a one-cycle pulse. Polling for it
      from the main loop can miss it, so a background monitor coroutine
      latches it ([[tb-structure]]: background monitors for async
      outputs). The per-channel `crc_valid` outputs are sticky levels
      by contrast, so those are safe to read at the end.
    """

    def __init__(self, dut):
        super().__init__(dut)

        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate')
        self.NUM_CH = self.convert_to_int(
            os.environ.get('TEST_NUM_CHANNELS', '4'))
        self.DW = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '512'))

        # Beats per channel scales with level; the scenario list itself
        # is the same at every level so the contract is always pinned.
        self.beats = {'gate': 32, 'func': 64, 'full': 256}.get(
            self.TEST_LEVEL, 32)

        self.errors = 0
        self._done_seen = False
        self._done_monitor = None
        self._bp_task = None

    # ---- three mandatory TB methods (GLOBAL_REQUIREMENTS 2.2) ----------

    async def setup_clocks_and_reset(self):
        """Start the clock, park config, and reset.

        Config is parked BEFORE reset is released because both blocks
        sample their cfg inputs when they see the start pulse; leaving
        stale values here is how a run silently streams zero beats.
        """
        await self.start_clock('clk', 10, 'ns')

        self.dut.cfg_start_chk.value = 0
        self.dut.cfg_start_gen.value = 0
        self.dut.cfg_lfsr_seed.value = 0
        self.dut.cfg_channel_mask.value = 0
        self.dut.cfg_num_beats.value = 0
        self.dut.cfg_beats_per_pkt.value = 0
        self.dut.cfg_tdest.value = 0
        self.dut.chk_backpressure.value = 0

        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

        self.log.info(f"@ {get_sim_time('ns')}ns: axis4 pattern pair TB ready: "
                      f"NUM_CHANNELS={self.NUM_CH} DW={self.DW} "
                      f"level={self.TEST_LEVEL} beats/ch={self.beats}")

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    # ---- background monitors -------------------------------------------

    async def _monitor_gen_done(self):
        """Latch the generator's one-cycle cfg_done pulse."""
        while True:
            await RisingEdge(self.dut.clk)
            if int(self.dut.gen_done.value) == 1:
                self._done_seen = True
                self.log.debug(f"@ {get_sim_time('ns')}ns: gen_done pulse")

    async def _drive_backpressure(self, pattern):
        """Toggle the checker's ready gate through (on, cycles) pairs,
        repeating until stopped."""
        while True:
            for on, cycles in pattern:
                self.dut.chk_backpressure.value = 1 if on else 0
                await self.wait_clocks('clk', cycles)

    # ---- scenario -------------------------------------------------------

    async def run_stream(self, *, beats, beats_per_pkt, mask=0, seed=0xACE1_2345,
                         backpressure=None, label=""):
        # Full reset between scenarios: the checker's counters only clear
        # on reset or on its start pulse, and its CRC is cumulative.
        await self.assert_reset()
        await self.wait_clocks('clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

        self._done_seen = False
        if self._done_monitor is None:
            self._done_monitor = cocotb.start_soon(self._monitor_gen_done())

        self.dut.cfg_lfsr_seed.value = seed
        self.dut.cfg_channel_mask.value = mask
        self.dut.cfg_num_beats.value = beats
        self.dut.cfg_beats_per_pkt.value = beats_per_pkt
        self.dut.cfg_tdest.value = 0
        self.dut.chk_backpressure.value = 0
        await self.wait_clocks('clk', 2)

        if backpressure:
            self._bp_task = cocotb.start_soon(
                self._drive_backpressure(backpressure))

        # Arm the checker first, then start the generator. One cycle each
        # -- these are pulses (see the class docstring).
        self.dut.cfg_start_chk.value = 1
        await self.wait_clocks('clk', 1)
        self.dut.cfg_start_chk.value = 0
        await self.wait_clocks('clk', 1)
        self.dut.cfg_start_gen.value = 1
        await self.wait_clocks('clk', 1)
        self.dut.cfg_start_gen.value = 0

        # Bound the wait generously: with backpressure the stream is
        # deliberately slow, and a hang here is itself a failure.
        limit = max(20_000, beats * self.NUM_CH * 40)
        waited = 0
        while not self._done_seen and waited < limit:
            await self.wait_clocks('clk', 1)
            waited += 1

        if self._bp_task is not None:
            self._bp_task.kill()
            self._bp_task = None
        self.dut.chk_backpressure.value = 0

        if not self._done_seen:
            self.log.error(f"@ {get_sim_time('ns')}ns: [{label}] generator "
                           f"never signalled done within {limit} cycles")
            self.errors += 1
            return

        # Let the tail drain into the checker before reading counters.
        await self.wait_clocks('clk', 200)
        self.check_results(beats=beats, beats_per_pkt=beats_per_pkt,
                           mask=mask, label=label)

    def check_results(self, *, beats, beats_per_pkt, mask, label):
        active = [c for c in range(self.NUM_CH)
                  if mask == 0 or (mask >> c) & 1]
        expected_total = beats * len(active)

        gen_total = int(self.dut.gen_beat_count_total.value)
        chk_total = int(self.dut.chk_beat_count_total.value)

        # Prove traffic happened before trusting any "no error" signal.
        if chk_total == 0:
            self.log.error(f"@ {get_sim_time('ns')}ns: [{label}] checker saw "
                           f"zero beats; the loop never ran")
            self.errors += 1
            return
        if gen_total != expected_total:
            self.log.error(f"@ {get_sim_time('ns')}ns: [{label}] generator "
                           f"sent {gen_total} beats, expected {expected_total}")
            self.errors += 1
        if chk_total != gen_total:
            self.log.error(f"@ {get_sim_time('ns')}ns: [{label}] checker saw "
                           f"{chk_total} beats, generator sent {gen_total}")
            self.errors += 1
        if int(self.dut.o_data_error.value) != 0:
            self.log.error(f"@ {get_sim_time('ns')}ns: [{label}] checker "
                           f"asserted o_data_error")
            self.errors += 1

        gen_crc = self.dut.gen_expected_crc.value
        chk_crc = self.dut.chk_actual_crc.value
        gen_v = int(self.dut.gen_expected_crc_valid.value)
        chk_v = int(self.dut.chk_actual_crc_valid.value)

        for c in active:
            g = int(gen_crc[self.NUM_CH - 1 - c])
            a = int(chk_crc[self.NUM_CH - 1 - c])
            gv, av = (gen_v >> c) & 1, (chk_v >> c) & 1
            if not gv or not av:
                self.log.error(f"@ {get_sim_time('ns')}ns: [{label}] ch{c}: "
                               f"crc_valid gen={gv} chk={av}")
                self.errors += 1
            elif g != a:
                self.log.error(f"@ {get_sim_time('ns')}ns: [{label}] ch{c}: "
                               f"CRC mismatch gen=0x{g:08X} chk=0x{a:08X}")
                self.errors += 1

        if beats_per_pkt:
            exp_pkts = (beats // beats_per_pkt) * len(active)
            got_pkts = int(self.dut.o_pkt_count.value)
            if got_pkts != exp_pkts:
                self.log.error(f"@ {get_sim_time('ns')}ns: [{label}] packet "
                               f"count {got_pkts}, expected {exp_pkts}")
                self.errors += 1

        self.log.info(f"@ {get_sim_time('ns')}ns: [{label}] {chk_total} beats "
                      f"over {len(active)} channel(s), CRCs agreed")

    # ---- entry point -----------------------------------------------------

    async def run_all(self):
        n = self.beats

        # Baseline: every channel, clean stream.
        await self.run_stream(beats=n, beats_per_pkt=8, label="baseline")

        # Single channel via the mask.
        await self.run_stream(beats=n // 2, beats_per_pkt=8, mask=0x1,
                              label="ch0-only")

        # Backpressure: a generator that ignored tready would desync the
        # LFSR and break CRC agreement.
        await self.run_stream(beats=n, beats_per_pkt=8,
                              backpressure=[(True, 40), (False, 20)],
                              label="backpressure")

        # A different seed must still agree, and shows the CRC tracks the
        # data rather than being a constant.
        await self.run_stream(beats=n // 2, beats_per_pkt=8,
                              seed=0x1234_5678, label="alt-seed")

        # Smallest interesting case: exactly one packet.
        await self.run_stream(beats=8, beats_per_pkt=8, label="single-packet")

        if self.TEST_LEVEL == 'full':
            rng = random.Random(self.SEED)
            for i in range(4):
                await self.run_stream(
                    beats=rng.choice((16, 32, 64)),
                    beats_per_pkt=rng.choice((4, 8, 16)),
                    mask=rng.randrange(1, 1 << self.NUM_CH),
                    seed=rng.randrange(1 << 32),
                    label=f"random-{i}")

        assert self.errors == 0, \
            f"{self.errors} error(s) in the pattern generator/checker loop"
        self.log.info(f"@ {get_sim_time('ns')}ns: axis4 pattern pair: "
                      f"generator and checker agree in all modes")
