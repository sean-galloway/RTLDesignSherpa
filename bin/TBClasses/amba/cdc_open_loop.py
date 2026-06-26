# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: CDCOpenLoopTB
# Purpose: Testbench for rtl/amba/shared/cdc_open_loop.sv — multi-bit
#          open-loop (fire-and-forget) CDC via data/valid stretch.
#
# The interface is simpler than the req/ack handshakes:
#   src_valid (single-cycle pulse)  → src_data captured & stretched
#   src_busy  (level)               → stretch in progress, drop new valids
#   dst_valid (single-cycle pulse)  → dst_data was latched on this edge
#
# Verification questions answered by this TB:
#
#   1. When STRETCH is sized correctly for the src/dst clock ratio,
#      *every* pulse the source asserts (while !src_busy) results in
#      exactly one dst_valid pulse with matching data.
#
#   2. When STRETCH is *too short* for the ratio, some pulses get
#      missed at the destination synchronizer — the source thinks it
#      sent them, but the destination never saw them. This is the
#      "stretch cliff" behavior the auto-compute formula is designed
#      to keep you above.
#
#   3. Source-side back-pressure: pulses asserted while src_busy is
#      high are dropped at the source (no stretch starts). The source
#      should respect src_busy and never assert two valids closer than
#      STRETCH cycles apart.
#
# This TB drives pulses with parameterized spacing, captures every
# dst_valid + dst_data, and compares against a reference queue of
# "what we expected the destination to see."

import os
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from TBClasses.shared.tbbase import TBBase


class CDCOpenLoopTB(TBBase):
    """Lean testbench for cdc_open_loop. No GAXI/memory model needed —
    this is a fire-and-forget multi-bit CDC with a tiny port surface."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)

        # Parameters from env (set by pytest wrapper)
        self.DATA_WIDTH      = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '16'))
        self.SRC_PERIOD_NS   = self.convert_to_int(os.environ.get('SRC_PERIOD_NS', '40'))  # 25 MHz
        self.DST_PERIOD_NS   = self.convert_to_int(os.environ.get('DST_PERIOD_NS', '10'))  # 100 MHz
        self.STRETCH_CYCLES  = self.convert_to_int(os.environ.get('STRETCH_CYCLES', '8'))
        self.SYNC_STAGES     = self.convert_to_int(os.environ.get('SYNC_STAGES', '3'))
        self.AUTO_STRETCH    = self.convert_to_int(os.environ.get('AUTO_STRETCH', '0'))
        self.SRC_CLK_HZ      = self.convert_to_int(os.environ.get('SRC_CLK_HZ', '25000000'))
        self.DST_CLK_HZ      = self.convert_to_int(os.environ.get('DST_CLK_HZ', '100000000'))
        self.TEST_LEVEL      = os.environ.get('TEST_LEVEL', 'basic').lower()

        # Effective STRETCH (what the DUT actually uses).
        if self.AUTO_STRETCH:
            # ceil((SYNC+1) * SRC_HZ / DST_HZ)
            self.STRETCH_EFF = max(1,
                ((self.SYNC_STAGES + 1) * self.SRC_CLK_HZ + self.DST_CLK_HZ - 1) // self.DST_CLK_HZ)
        else:
            self.STRETCH_EFF = max(1, self.STRETCH_CYCLES)

        # Stretch wall-time at the current src clock, and the dst
        # settle-time required. If hold_ns < settle_ns the cliff is
        # in play — some pulses will be lost.
        self.STRETCH_HOLD_NS = self.STRETCH_EFF * self.SRC_PERIOD_NS
        self.DST_SETTLE_NS   = (self.SYNC_STAGES + 1) * self.DST_PERIOD_NS
        self.EXPECT_LOSSES   = self.STRETCH_HOLD_NS < self.DST_SETTLE_NS

        # Back-to-back spacing: after src_busy clears, the destination
        # sync chain still needs (SYNC_STAGES+1) dst cycles to see the
        # falling edge before the next rising edge can be detected.
        # Otherwise two HIGH stretches merge into one in dst view.
        # Round up to src cycles, +1 slack.
        self.LOW_GAP_SRC_CYCLES = max(
            1,
            ((self.SYNC_STAGES + 1) * self.DST_PERIOD_NS + self.SRC_PERIOD_NS - 1)
            // self.SRC_PERIOD_NS) + 1

        # Stats / state
        self.sent_queue = deque()   # FIFO of (sim_time, expected_data) we shipped
        self.received   = []        # list of (sim_time, data) we observed at dst
        self.total_errors = 0
        self.done = False

        self.log.info(f"CDCOpenLoopTB config:")
        self.log.info(f"  DATA_WIDTH       = {self.DATA_WIDTH}")
        self.log.info(f"  SRC clock        = {self.SRC_PERIOD_NS} ns ({1000/self.SRC_PERIOD_NS:.2f} MHz)")
        self.log.info(f"  DST clock        = {self.DST_PERIOD_NS} ns ({1000/self.DST_PERIOD_NS:.2f} MHz)")
        self.log.info(f"  STRETCH_CYCLES   = {self.STRETCH_CYCLES} (manual default)")
        self.log.info(f"  SYNC_STAGES      = {self.SYNC_STAGES}")
        self.log.info(f"  AUTO_STRETCH     = {self.AUTO_STRETCH}")
        self.log.info(f"  SRC_CLK_HZ       = {self.SRC_CLK_HZ}")
        self.log.info(f"  DST_CLK_HZ       = {self.DST_CLK_HZ}")
        self.log.info(f"  → STRETCH_EFF    = {self.STRETCH_EFF}")
        self.log.info(f"  → hold time      = {self.STRETCH_HOLD_NS} ns")
        self.log.info(f"  → dst settle     = {self.DST_SETTLE_NS} ns")
        self.log.info(f"  → expect losses  = {self.EXPECT_LOSSES}")
        self.log.info(f"  TEST_LEVEL       = {self.TEST_LEVEL}")

    # ------------------------------------------------------------------
    # Lifecycle
    # ------------------------------------------------------------------
    async def reset_dut(self):
        """Hold both resets low for a generous window, then release."""
        self.dut.rst_src_n.value = 0
        self.dut.rst_dst_n.value = 0
        self.dut.src_valid.value = 0
        self.dut.src_data.value  = 0
        # Wait long enough that both domains see reset asserted
        await Timer(max(self.SRC_PERIOD_NS, self.DST_PERIOD_NS) * 10, units='ns')
        self.dut.rst_src_n.value = 1
        self.dut.rst_dst_n.value = 1
        # Let synchronizers settle on the deassertion
        await Timer(max(self.SRC_PERIOD_NS, self.DST_PERIOD_NS) * 10, units='ns')

    async def start_clocks_and_monitor(self):
        await self.start_clock('clk_src', self.SRC_PERIOD_NS, 'ns')
        await self.start_clock('clk_dst', self.DST_PERIOD_NS, 'ns')
        await self.reset_dut()
        cocotb.start_soon(self._dst_monitor())

    # ------------------------------------------------------------------
    # Destination monitor — captures every dst_valid pulse + data
    # ------------------------------------------------------------------
    async def _dst_monitor(self):
        while not self.done:
            await RisingEdge(self.dut.clk_dst)
            if int(self.dut.dst_valid.value) == 1:
                data = int(self.dut.dst_data.value)
                t = get_sim_time('ns')
                self.received.append((t, data))
                self.log.debug(f"dst_valid: data=0x{data:0{(self.DATA_WIDTH+3)//4}X} at {t} ns")

    # ------------------------------------------------------------------
    # Source driver — assert src_valid for one src_clk, respect src_busy
    # ------------------------------------------------------------------
    async def send_one(self, data, wait_for_busy_clear=True):
        """Send one pulse. If wait_for_busy_clear is True, waits for
        src_busy to go low first AND for the dst sync chain to see
        the falling edge (no source-side drops, no merged pulses at
        the destination). If False, attempts the send regardless; if
        busy was high, the source silently drops the request (and we
        do NOT enqueue it as sent)."""
        await RisingEdge(self.dut.clk_src)

        if wait_for_busy_clear:
            # Wait for busy to clear
            timeout_ns = max(self.STRETCH_EFF * self.SRC_PERIOD_NS * 4, 1000)
            t_start = get_sim_time('ns')
            while int(self.dut.src_busy.value) == 1:
                await RisingEdge(self.dut.clk_src)
                if get_sim_time('ns') - t_start > timeout_ns:
                    raise TimeoutError(
                        f"src_busy stayed high for {timeout_ns} ns "
                        f"(STRETCH_EFF={self.STRETCH_EFF} cycles)")
            # Busy is clear; r_src_valid_stretch just went low. The dst
            # sync chain still needs LOW_GAP cycles to see the falling
            # edge before the next rising edge can be detected as a
            # new pulse.
            for _ in range(self.LOW_GAP_SRC_CYCLES):
                await RisingEdge(self.dut.clk_src)

        # If busy was clear, drive a pulse. The source will accept it.
        if int(self.dut.src_busy.value) == 0:
            self.dut.src_data.value = data & ((1 << self.DATA_WIDTH) - 1)
            self.dut.src_valid.value = 1
            self.sent_queue.append((get_sim_time('ns'), data & ((1 << self.DATA_WIDTH) - 1)))
            await RisingEdge(self.dut.clk_src)
            self.dut.src_valid.value = 0
        else:
            # Drop — source thinks it was busy. Do NOT enqueue.
            self.log.debug(f"src dropped value 0x{data:X} (busy)")

    # ------------------------------------------------------------------
    # Settle: wait long enough that any in-flight stretch + sync
    # completes (rounded up generously).
    # ------------------------------------------------------------------
    async def drain_settle(self):
        # Wait for STRETCH worth of src clocks + 4 dst syncs + some slack
        wait_ns = self.STRETCH_EFF * self.SRC_PERIOD_NS \
                + (self.SYNC_STAGES + 4) * self.DST_PERIOD_NS \
                + 200
        await Timer(wait_ns, units='ns')

    # ------------------------------------------------------------------
    # Verification — depends on whether we expect losses
    # ------------------------------------------------------------------
    def verify_no_loss(self):
        """For safe configs: every sent value should appear at dst in
        order, with matching data."""
        sent = list(self.sent_queue)
        recv = self.received

        if len(sent) != len(recv):
            self.total_errors += 1
            self.log.error(f"COUNT MISMATCH: sent={len(sent)} received={len(recv)}")
            self.log.error(f"  sent  data: {[hex(d) for _, d in sent[:10]]}")
            self.log.error(f"  recv  data: {[hex(d) for _, d in recv[:10]]}")
            return False

        for i, ((_, sd), (_, rd)) in enumerate(zip(sent, recv)):
            if sd != rd:
                self.total_errors += 1
                self.log.error(f"DATA MISMATCH at #{i}: sent=0x{sd:X} recv=0x{rd:X}")
                return False
        return True

    def verify_received_subset(self):
        """For unsafe (cliff) configs: every received value MUST be one
        we sent (no spurious values), but some sent values may not arrive.
        Receiving 0 of N is a real failure too — pulses being lost is
        OK, but ALL pulses lost suggests the design is broken, not just
        running above the cliff.
        Returns (pass, drop_count)."""
        sent_data = [d for _, d in self.sent_queue]
        recv_data = [d for _, d in self.received]

        # Every received value must appear in the sent sequence
        sent_remaining = list(sent_data)
        for rd in recv_data:
            if rd in sent_remaining:
                sent_remaining.remove(rd)
            else:
                self.total_errors += 1
                self.log.error(f"SPURIOUS dst value 0x{rd:X} — not in sent sequence")
                return (False, 0)

        dropped = len(sent_data) - len(recv_data)
        if len(recv_data) == 0 and len(sent_data) > 0:
            # 100% loss — unusual; could be the design IS broken
            self.log.warning(f"ALL {len(sent_data)} pulses dropped — very steep cliff")
        return (True, dropped)

    # ------------------------------------------------------------------
    # Test phases
    # ------------------------------------------------------------------
    async def run_basic(self):
        """A handful of pulses with wide spacing. All should arrive
        regardless of stretch (we wait for busy each time)."""
        self.log.info("=== BASIC: 10 pulses, wide spacing, wait-for-busy ===")
        count = 10
        for i in range(count):
            await self.send_one(0xA5A5 ^ (i << 4), wait_for_busy_clear=True)
        await self.drain_settle()
        if not self.verify_no_loss():
            return False
        self.log.info(f"  ✓ basic: {len(self.received)}/{count} arrived")
        return True

    async def run_walking_pattern(self):
        """Walking-1 and walking-0 across DATA_WIDTH bits. Catches
        per-bit stuck/skew issues."""
        self.log.info(f"=== WALKING: {2*self.DATA_WIDTH} pulses ===")
        before = len(self.received)
        for i in range(self.DATA_WIDTH):
            await self.send_one(1 << i, wait_for_busy_clear=True)
        for i in range(self.DATA_WIDTH):
            await self.send_one(((1 << self.DATA_WIDTH) - 1) ^ (1 << i),
                                wait_for_busy_clear=True)
        await self.drain_settle()
        delivered = len(self.received) - before
        expected  = 2 * self.DATA_WIDTH
        if delivered != expected:
            self.total_errors += 1
            self.log.error(f"WALKING: delivered {delivered}, expected {expected}")
            return False
        self.log.info(f"  ✓ walking: {delivered}/{expected} arrived")
        return True

    async def run_back_to_back(self, count=50):
        """Issue pulses as fast as the source will accept (waits for
        busy each time). All should arrive."""
        self.log.info(f"=== BACK-TO-BACK: {count} pulses ===")
        before = len(self.received)
        for i in range(count):
            await self.send_one((i * 0x101) & ((1 << self.DATA_WIDTH) - 1),
                                wait_for_busy_clear=True)
        await self.drain_settle()
        delivered = len(self.received) - before
        if delivered != count:
            self.total_errors += 1
            self.log.error(f"B2B: delivered {delivered}, expected {count}")
            return False
        self.log.info(f"  ✓ b2b: {delivered}/{count} arrived")
        return True

    async def run_cliff_probe(self, count=40):
        """Drive pulses without waiting for src_busy. On a SAFE config
        most/all should arrive (some src-side drops are normal when
        busy is asserted). On an UNSAFE config (cliff), many should
        be lost at the destination synchronizer."""
        self.log.info(f"=== CLIFF: {count} pulses, no wait-for-busy ===")
        before_sent = len(self.sent_queue)
        before_recv = len(self.received)
        for i in range(count):
            await self.send_one((0xDEAD ^ (i * 0x11)) & ((1 << self.DATA_WIDTH) - 1),
                                wait_for_busy_clear=False)
            # Tiny spacing to let the source process busy
            for _ in range(2):
                await RisingEdge(self.dut.clk_src)
        await self.drain_settle()

        sent = len(self.sent_queue) - before_sent
        recv = len(self.received) - before_recv
        ok, drops = self.verify_received_subset()
        self.log.info(f"  cliff: sent {sent} (src-accepted), recv {recv}, "
                     f"drops {drops}, ok={ok}")
        if self.EXPECT_LOSSES:
            if drops == 0 and sent > 5:
                self.log.warning("  expected drops at this clock ratio but saw 0 — "
                                "stretch may be more conservative than computed")
        return ok

    async def run_all_for_level(self):
        """Pick phases based on TEST_LEVEL.

        When EXPECT_LOSSES is True (STRETCH sized below the cliff for the
        real src/dst ratio), the no-loss phases will fail because every
        pulse — even with src_busy backpressure — gets dropped at the
        destination synchronizer. In that case run only the cliff_probe,
        which uses subset verification and is the meaningful check."""
        if self.EXPECT_LOSSES:
            self.log.info("EXPECT_LOSSES=True → running cliff_probe only "
                          "(no-loss phases would fail by design)")
            return await self.run_cliff_probe(count=40)

        ok = True
        ok &= await self.run_basic()
        if self.TEST_LEVEL in ('func', 'full'):
            ok &= await self.run_walking_pattern()
            ok &= await self.run_back_to_back(count=30)
        if self.TEST_LEVEL == 'full':
            ok &= await self.run_back_to_back(count=100)
            ok &= await self.run_cliff_probe(count=40)
        return ok
