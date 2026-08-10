# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: arbiter_token_bucket_tb
# Purpose: Testbench class for the token-bucket request shaper
#
# Documentation: docs/markdown/rtl-common/index.md
# Subsystem: TBClasses/common
#
# Author: sean galloway
# Created: 2026-08-10

"""
Token-Bucket Request Shaper Testbench

The shaper's contract: cumulative completed grants per client can NEVER
exceed cumulative refilled tokens (buckets start empty), the burst allowance
is exactly the cap, and a cap-0 client is unshaped (fail-open bypass).

The TB plays the DOWNSTREAM ARBITER: it samples request_out each cycle and
grants one passing requester (rotating pick), registered one cycle later
exactly as the real arbiters present their grant. That timing matters - the
overspend window the shaper's net-of-spend gate closes only exists with a
registered grant.

The never-overspend check is an INVARIANT asserted every completion, not a
statistic: one violation fails the run.
"""

import os
import random

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase


class TokenBucketTB(TBBase):
    """Testbench for arbiter_token_bucket."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.dut = dut

        self.CLIENTS = self.convert_to_int(os.environ.get('TEST_CLIENTS', '4'))
        self.MAX_TOKENS = self.convert_to_int(os.environ.get('TEST_MAX_TOKENS', '64'))
        self.RATE_WIDTH = self.convert_to_int(os.environ.get('TEST_RATE_WIDTH', '4'))
        self.WAIT_GNT_ACK = self.convert_to_int(os.environ.get('TEST_WAIT_GNT_ACK', '0'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)

        self.TW = max(1, (self.MAX_TOKENS - 1).bit_length())

        # Live config mirrors
        self.rates = [1] * self.CLIENTS
        self.caps = [8] * self.CLIENTS

        # Scoreboard: the never-overspend ledger
        self.refilled = [0] * self.CLIENTS     # cumulative tokens granted by ticks
        self.completed = [0] * self.CLIENTS    # cumulative completed grants
        self.violations = []

        self._rr_pick = 0                      # TB-arbiter rotate pointer

    # ------------------------------------------------------------------
    # Mandatory TB methods
    # ------------------------------------------------------------------

    async def setup_clocks_and_reset(self):
        await self.start_clock('clk', 10, 'ns')
        self.dut.refill_tick.value = 0
        self.dut.request_in.value = 0
        self.dut.grant.value = 0
        self.dut.grant_valid.value = 0
        self.dut.grant_ack.value = 0
        self.apply_config()
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    # ------------------------------------------------------------------
    # Config and ledger
    # ------------------------------------------------------------------

    def _pack(self, vals, width):
        packed = 0
        for i, v in enumerate(vals):
            packed |= (int(v) & ((1 << width) - 1)) << (i * width)
        return packed

    def apply_config(self, rates=None, caps=None):
        if rates is not None:
            self.rates = list(rates)
        if caps is not None:
            self.caps = list(caps)
        self.dut.rate.value = self._pack(self.rates, self.RATE_WIDTH)
        self.dut.bucket_cap.value = self._pack(self.caps, self.TW)

    def _ledger_refill(self):
        """Mirror one refill tick: shaped clients gain rate, saturating at
        cap MINUS what they hold - the ledger tracks the REFILL actually
        banked, which under saturation of the bucket is less than rate."""
        # The ledger cannot see the RTL bucket level without reading the
        # observability port - use it (that is what it is for)
        packed = int(self.dut.tokens.value)
        for i in range(self.CLIENTS):
            if self.caps[i] == 0:
                continue    # bypass client: tokens are meaningless
            held = (packed >> (i * self.TW)) & ((1 << self.TW) - 1)
            banked = min(self.rates[i], max(0, self.caps[i] - held))
            self.refilled[i] += banked
            if os.environ.get('TB_DEBUG_LEDGER') and i == 1:
                self.log.info(f"LEDGER refill c1: held={held} banked={banked} "
                              f"refilled={self.refilled[1]} "
                              f"completed={self.completed[1]}")

    def check_never_overspent(self, client, where):
        if self.caps[client] == 0:
            return      # bypass client is exempt by design
        if self.completed[client] > self.refilled[client]:
            packed = int(self.dut.tokens.value)
            held = (packed >> (client * self.TW)) & ((1 << self.TW) - 1)
            if not self.violations:
                self.log.error(
                    f"LEDGER first violation {where}: client {client} "
                    f"completed={self.completed[client]} "
                    f"refilled={self.refilled[client]} rtl_held={held} "
                    f"rate={self.rates[client]} cap={self.caps[client]}")
            self.violations.append(
                f"{where}: client {client} completed "
                f"{self.completed[client]} > refilled {self.refilled[client]}")

    # ------------------------------------------------------------------
    # The TB-side arbiter + traffic engine
    # ------------------------------------------------------------------

    async def run_traffic(self, cycles, tick_period, requesters=None):
        """Drive saturated requests for `requesters` and play the downstream
        arbiter: grant one passing request_out per cycle, REGISTERED (grant
        asserted the cycle after the pick), ACK per WAIT_GNT_ACK."""
        req_mask = ((1 << self.CLIENTS) - 1) if requesters is None else 0
        if requesters is not None:
            for i in requesters:
                req_mask |= (1 << i)

        self.dut.request_in.value = req_mask
        pending_grant = 0
        tick_count = 0

        for cycle in range(cycles):
            # Refill cadence
            tick_now = (cycle % tick_period) == 0 and cycle > 0
            if tick_now:
                self._ledger_refill()   # reads pre-tick bucket levels
            self.dut.refill_tick.value = 1 if tick_now else 0

            # Drive this cycle's grant (registered: picked LAST cycle)
            self.dut.grant.value = pending_grant
            self.dut.grant_valid.value = 1 if pending_grant else 0
            if self.WAIT_GNT_ACK == 1:
                # ack in the same cycle the grant shows - completion on this
                # edge, minimal-latency consumer
                self.dut.grant_ack.value = pending_grant
            await RisingEdge(self.dut.clk)
            # Settle: request_out/tokens are combinational off the just-updated
            # registers - sampling in the same delta reads PRE-edge values and
            # the TB-arbiter then picks winners from a stale gate (spends
            # appeared one cycle late in the trace; the overspend was the TB's,
            # not the RTL's)
            await Timer(100, units='ps')

            # Completion accounting (this edge committed the spend)
            if pending_grant:
                gid = pending_grant.bit_length() - 1
                self.completed[gid] += 1
                if tick_now:
                    tick_count += 1
                self.check_never_overspent(gid, f"cycle {cycle}")

            # Play the arbiter: pick next winner from the shaped requests
            shaped = int(self.dut.request_out.value)
            if os.environ.get('TB_DEBUG_LEDGER') and cycle < 100:
                packed_t = int(self.dut.tokens.value)
                mask_t = (1 << self.TW) - 1
                held_dbg = [(packed_t >> (i * self.TW)) & mask_t
                            for i in range(self.CLIENTS)]
                self.log.info(f"CYC {cycle}: tick={int(tick_now)} "
                              f"grant={pending_grant:0{self.CLIENTS}b} "
                              f"shaped={shaped:0{self.CLIENTS}b} held={held_dbg}")
            pending_grant = 0
            if shaped:
                for k in range(self.CLIENTS):
                    idx = (self._rr_pick + k) % self.CLIENTS
                    if (shaped >> idx) & 1:
                        pending_grant = 1 << idx
                        self._rr_pick = (idx + 1) % self.CLIENTS
                        break

        # Quiesce
        self.dut.request_in.value = 0
        self.dut.grant.value = 0
        self.dut.grant_valid.value = 0
        self.dut.grant_ack.value = 0
        self.dut.refill_tick.value = 0
        await self.wait_clocks('clk', 5)

    def clear_ledger(self):
        """Start a scenario's ledger from the OBSERVED bucket levels, not
        zero - tokens banked in an earlier scenario are real spending budget
        (the RTL carries them; a zeroed ledger reads legitimate spends as
        overspend - found as phantom violations the moment scenarios ran
        back-to-back, the same lesson as the DRR mirror's drain clear)."""
        packed = int(self.dut.tokens.value)
        mask = (1 << self.TW) - 1
        self.refilled = [(packed >> (i * self.TW)) & mask
                         for i in range((self.CLIENTS))]
        self.completed = [0] * self.CLIENTS

    # ------------------------------------------------------------------
    # Scenarios
    # ------------------------------------------------------------------

    async def scenario_sustained_rate(self, cycles, tick_period=16):
        """Saturated requests: each shaped client's completions track its
        refill exactly (never above; within one bucket of it below)."""
        rates = [(i % 3) + 1 for i in range(self.CLIENTS)]
        # Caps live in a TW-bit field: 8 with MAX_TOKENS=8 would wrap to 0,
        # which means BYPASS - the one value a shaping test must not drive
        caps = [min(8, self.MAX_TOKENS - 1)] * self.CLIENTS
        self.apply_config(rates, caps)
        self.clear_ledger()
        await self.run_traffic(cycles, tick_period)
        assert not self.violations, f"overspend: {self.violations[:5]}"
        for i in range(self.CLIENTS):
            assert self.completed[i] <= self.refilled[i], \
                f"client {i}: {self.completed[i]} > refill {self.refilled[i]}"
            # Under saturation the client consumes what it is given, minus at
            # most one bucketful still banked at the end
            assert self.completed[i] >= self.refilled[i] - caps[i], \
                (f"sustained_rate: client {i} badly under-served: "
                 f"{self.completed[i]} vs refilled {self.refilled[i]}")
            self.log.info(f"sustained_rate: client {i} rate={rates[i]} "
                          f"completed={self.completed[i]} refilled={self.refilled[i]}")

    async def scenario_burst_allowance(self, tick_period=8):
        """An idle client accumulates to cap, then bursts EXACTLY cap grants
        back-to-back before throttling to the refill rate."""
        cap = min(6, self.MAX_TOKENS - 1)
        rates = [1] * self.CLIENTS
        caps = [cap] * self.CLIENTS
        self.apply_config(rates, caps)
        self.clear_ledger()

        # Fill client 0's bucket with ticks while NOBODY requests
        for _ in range(cap * tick_period + 2):
            self.dut.refill_tick.value = 1
            await RisingEdge(self.dut.clk)
            self.dut.refill_tick.value = 0
            for _ in range(tick_period - 1):
                await RisingEdge(self.dut.clk)

        await Timer(100, units='ps')
        packed = int(self.dut.tokens.value)
        held = packed & ((1 << self.TW) - 1)
        assert held == cap, f"burst: bucket filled to {held}, expected cap {cap}"

        # Sole requester, NO refill ticks: burst length == cap exactly
        self.clear_ledger()             # ledger syncs to the banked cap
        await self.run_traffic(cap * 4 + 10, tick_period=10**9, requesters=[0])
        assert self.completed[0] == cap, \
            f"burst: served {self.completed[0]} on a {cap}-token bucket"
        assert not self.violations, f"burst overspend: {self.violations[:5]}"

    async def scenario_bypass(self, cycles):
        """cap 0 = unshaped: the client is granted freely with no ticks."""
        rates = [1] * self.CLIENTS
        caps = [4] * self.CLIENTS
        caps[self.CLIENTS - 1] = 0      # fail-open client
        self.apply_config(rates, caps)
        self.clear_ledger()
        carried = sum(self.refilled[:self.CLIENTS - 1])  # banked pre-scenario
        await self.run_traffic(cycles, tick_period=10**9)  # no refills ever
        bypass_served = self.completed[self.CLIENTS - 1]
        shaped_served = sum(self.completed[:self.CLIENTS - 1])
        assert bypass_served > cycles // 2, \
            (f"bypass: unshaped client served only {bypass_served} "
             f"of {cycles} cycles")
        assert shaped_served <= carried, \
            (f"bypass: shaped clients served {shaped_served} with no refills "
             f"and only {carried} banked tokens")
        assert not self.violations, f"bypass overspend: {self.violations[:5]}"

    async def scenario_rate_zero_drain(self, tick_period=8):
        """Runtime config change: rate drops to 0 mid-run - the client
        spends what it holds, then blocks. No FSM, clamp semantics."""
        cap = min(4, self.MAX_TOKENS - 1)
        self.apply_config([2] * self.CLIENTS, [cap] * self.CLIENTS)
        self.clear_ledger()
        await self.run_traffic(20 * tick_period, tick_period)
        served_before = self.completed[0]

        self.apply_config(rates=[0] * self.CLIENTS)   # cut all refill
        await self.run_traffic(20 * tick_period, tick_period)
        assert not self.violations, f"rate0 overspend: {self.violations[:5]}"

        # After the drain window every bucket must be empty: a further
        # window serves NOTHING (the never-overspend invariant bounded the
        # drain itself; this proves it actually terminates in a block)
        blocked_start = list(self.completed)
        await self.run_traffic(5 * tick_period, tick_period)
        for i in range(self.CLIENTS):
            post = self.completed[i] - blocked_start[i]
            assert post == 0, \
                f"rate0: client {i} served {post} grants after full drain"
        assert not self.violations, f"rate0 overspend: {self.violations[:5]}"
        self.log.info(f"rate0_drain: pre-cut client0={served_before}, "
                      f"post-drain fully blocked")
