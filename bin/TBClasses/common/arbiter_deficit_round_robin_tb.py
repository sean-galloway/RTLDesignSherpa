# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: arbiter_deficit_round_robin_tb
# Purpose: Testbench class for the deficit round-robin arbiter
#
# Documentation: docs/markdown/rtl-common/index.md
# Subsystem: TBClasses/common
#
# Author: sean galloway
# Created: 2026-08-09

"""
Deficit Round-Robin Arbiter Testbench

The DRR contract under test: long-run COST-UNITS served per client are
proportional to the client's quantum, whatever the per-request costs are.
That is the property that distinguishes it from the WRR sibling (whose
GRANT COUNTS are weight-proportional), so the scoreboard here counts served
cost, not grants.

Verification layers:
1. RoundRobinArbiterMonitor (framework) observes the grant stream -
   protocol-level transaction collection. Its RR-pattern analysis is NOT
   used: deficit gating legitimately reorders grants vs a plain RR.
2. A cycle mirror of the deficit discipline (same precedence as the RTL:
   request-drop clear, completion debit, replenish add) asserts that every
   grant went to a client whose deficit covered its cost.
3. Windowed share measurement: served-cost fractions vs quantum ratios.

NOTE: the mirror is TB-local for now. Promoting it into the RDS-DV
arbiter_monitor family (DeficitRoundRobinArbiterMonitor) is the follow-up
recorded in COMMON-007 - the framework model replays grants the same way
for RR/WRR today.
"""

import os
import random
from collections import deque

from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.arbiter_monitor import RoundRobinArbiterMonitor


class DeficitRoundRobinTB(TBBase):
    """Testbench for arbiter_deficit_round_robin."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.dut = dut

        self.CLIENTS = self.convert_to_int(os.environ.get('TEST_CLIENTS', '4'))
        self.MAX_QUANTUM = self.convert_to_int(os.environ.get('TEST_MAX_QUANTUM', '16'))
        self.COST_WIDTH = self.convert_to_int(os.environ.get('TEST_COST_WIDTH', '4'))
        self.WAIT_GNT_ACK = self.convert_to_int(os.environ.get('TEST_WAIT_GNT_ACK', '0'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)

        self.QW = max(1, (self.MAX_QUANTUM - 1).bit_length())
        self.MAX_COST = (1 << self.COST_WIDTH) - 1

        # Framework monitor: transaction observation only (no RR-pattern
        # analysis - deficit gating reorders grants vs plain RR by design)
        self.monitor = RoundRobinArbiterMonitor(
            dut=dut,
            title="DRR_Monitor",
            clock=self.dut.clk,
            reset_n=self.dut.rst_n,
            req_signal=self.dut.request,
            gnt_valid_signal=self.dut.grant_valid,
            gnt_signal=self.dut.grant,
            gnt_id_signal=self.dut.grant_id,
            gnt_ack_signal=self.dut.grant_ack,
            block_arb_signal=self.dut.block_arb,
            clients=self.CLIENTS,
            ack_mode=(self.WAIT_GNT_ACK == 1),
            log=self.log,
        )

        # Scoreboard state
        self.quanta = [1] * self.CLIENTS
        self.cur_cost = [1] * self.CLIENTS       # cost currently driven per client
        self.frames = [deque() for _ in range(self.CLIENTS)]  # pending frame costs
        self.served_cost = [0] * self.CLIENTS
        self.served_grants = [0] * self.CLIENTS

        # Deficit mirror (layer 2). The grant registers one cycle after the
        # arbitration that won it, so the mirror validates each grant against
        # ONE-DEEP HISTORY: the deficit and cost as of the arbitration cycle,
        # matching the RTL's cost pipeline.
        self.mirror_deficit = [0] * self.CLIENTS
        self.prev_deficit = [0] * self.CLIENTS
        self.prev_cost = [1] * self.CLIENTS
        self.mirror_enabled = True
        self.mirror_errors = []

    # ------------------------------------------------------------------
    # Mandatory TB methods
    # ------------------------------------------------------------------

    async def setup_clocks_and_reset(self):
        await self.start_clock('clk', 10, 'ns')
        self.dut.block_arb.value = 0
        self.dut.request.value = 0
        self.dut.grant_ack.value = 0
        self.dut.req_cost.value = 0
        self.dut.quantum.value = self._pack([1] * self.CLIENTS, self.QW)
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    # ------------------------------------------------------------------
    # Helpers
    # ------------------------------------------------------------------

    def _pack(self, vals, width):
        packed = 0
        for i, v in enumerate(vals):
            packed |= (int(v) & ((1 << width) - 1)) << (i * width)
        return packed

    async def set_quanta(self, quanta):
        """Drive new quanta and let the atomic-update FSM settle.

        The FSM path (BLOCK->DRAIN->UPDATE->STABILIZE) takes ~8 cycles idle
        but up to ~21 with the BLOCK timeout (a pending ACK-mode grant), and
        clears the RTL deficits at STABILIZE, so the mirror clears too.
        """
        assert len(quanta) == self.CLIENTS
        self.quanta = list(quanta)
        self.dut.quantum.value = self._pack(quanta, self.QW)
        await self.wait_clocks('clk', 30)
        self.mirror_deficit = [0] * self.CLIENTS
        self.prev_deficit = [0] * self.CLIENTS
        self.prev_cost = [1] * self.CLIENTS

    def _drive_requests(self):
        req = 0
        for i in range(self.CLIENTS):
            if self.frames[i]:
                req |= (1 << i)
                self.cur_cost[i] = self.frames[i][0]
        self.dut.request.value = req
        self.dut.req_cost.value = self._pack(self.cur_cost, self.COST_WIDTH)
        return req

    def _mirror_step(self, req_vec, completed_vec, pending_ack):
        """One cycle of the deficit discipline, same precedence as the RTL.

        A completion observed this cycle was ARBITRATED last cycle, so its
        affordability check and its debit both use the one-deep history
        (prev_deficit / prev_cost) - the mirror twin of the RTL cost
        pipeline. Replenish decisions use current-cycle state, as the RTL's
        combinational replenish does.
        """
        if not self.mirror_enabled:
            return
        affordable = [
            (req_vec >> i) & 1 and self.quanta[i] > 0
            and self.mirror_deficit[i] >= self._eff_cost(i)
            for i in range(self.CLIENTS)
        ]
        replenish = (req_vec != 0) and not any(affordable) and not pending_ack

        snapshot_deficit = list(self.mirror_deficit)
        snapshot_cost = [self._eff_cost(i) for i in range(self.CLIENTS)]

        for i in range(self.CLIENTS):
            if (completed_vec >> i) & 1:
                if self.prev_deficit[i] < self.prev_cost[i]:
                    if not self.mirror_errors:
                        self.log.error(
                            f"MIRROR first violation: client {i} "
                            f"completed={completed_vec:0{self.CLIENTS}b} "
                            f"req={req_vec:0{self.CLIENTS}b} "
                            f"prev_deficit={self.prev_deficit} "
                            f"prev_cost={self.prev_cost} "
                            f"mirror_deficit={self.mirror_deficit} "
                            f"replenish={replenish} quanta={self.quanta}")
                    self.mirror_errors.append(
                        f"grant to client {i} arbitrated with deficit "
                        f"{self.prev_deficit[i]} < cost {self.prev_cost[i]}")
                self.mirror_deficit[i] = max(
                    0, self.mirror_deficit[i] - self.prev_cost[i])
            elif not (req_vec >> i) & 1:
                self.mirror_deficit[i] = 0
            elif replenish and self.quanta[i] > 0:
                self.mirror_deficit[i] += self.quanta[i]

        self.prev_deficit = snapshot_deficit
        self.prev_cost = snapshot_cost

    def _eff_cost(self, i):
        c = self.cur_cost[i]
        return c if c > 0 else 1

    # ------------------------------------------------------------------
    # Traffic engine
    # ------------------------------------------------------------------

    async def run_traffic(self, target_completions, cost_fn, active=None,
                          refill=True):
        """Drive saturated traffic until target_completions grants complete.

        cost_fn(client) -> cost of that client's next frame (1..MAX_COST).
        active: iterable of client indices that carry traffic (default all).
        refill: keep every active client backlogged (saturation).
        """
        active = list(range(self.CLIENTS)) if active is None else list(active)

        for i in active:
            while len(self.frames[i]) < 4:
                self.frames[i].append(cost_fn(i))

        completions = 0
        ack_clear = 0
        timeout = target_completions * 200 + 2000

        for _ in range(timeout):
            self._drive_requests()
            await RisingEdge(self.dut.clk)

            gnt_valid = int(self.dut.grant_valid.value)
            gnt_vec = int(self.dut.grant.value) if gnt_valid else 0
            ack_vec = int(self.dut.grant_ack.value)
            req_vec = int(self.dut.request.value)

            if self.WAIT_GNT_ACK == 0:
                completed_vec = gnt_vec if gnt_valid else 0
                pending_ack = False
            else:
                completed_vec = gnt_vec & ack_vec
                pending_ack = bool(gnt_valid and not (gnt_vec & ack_vec))
                # ack the observed grant on the following cycle
                if ack_clear:
                    self.dut.grant_ack.value = 0
                    ack_clear = 0
                if gnt_valid and not (gnt_vec & ack_vec):
                    self.dut.grant_ack.value = gnt_vec
                    ack_clear = 1

            self._mirror_step(req_vec, completed_vec, pending_ack)

            for i in range(self.CLIENTS):
                if (completed_vec >> i) & 1:
                    completions += 1
                    if self.frames[i]:
                        cost = self.frames[i].popleft()
                        self.served_cost[i] += cost
                        self.served_grants[i] += 1
                    if refill and i in active:
                        while len(self.frames[i]) < 4:
                            self.frames[i].append(cost_fn(i))

            if completions >= target_completions:
                break
        else:
            raise AssertionError(
                f"traffic timeout: {completions}/{target_completions} "
                f"completions in {timeout} cycles")

        # Drain drive state. In ACK mode a grant may still be HELD awaiting
        # its ack (the base arbiter's contract) - complete it before leaving,
        # or it survives into the next scenario and completes against that
        # scenario's freshly-cleared mirror as a phantom violation.
        self.dut.request.value = 0
        for i in range(self.CLIENTS):
            self.frames[i].clear()
        if self.WAIT_GNT_ACK == 1:
            for _ in range(10):
                await RisingEdge(self.dut.clk)
                if int(self.dut.grant_valid.value):
                    self.dut.grant_ack.value = int(self.dut.grant.value)
                else:
                    self.dut.grant_ack.value = 0
                    break
        self.dut.grant_ack.value = 0
        await self.wait_clocks('clk', 5)
        # The mirror only steps inside the loop above, but the RTL keeps
        # applying the request-drop clear rule through these drained cycles:
        # with all requests low, every RTL deficit is now zero. Mirror the
        # clear, or the next traffic window starts against stale deficits
        # (found as seed-dependent phantom violations in anti_hoarding's
        # phase handoff - the one scenario transition with no set_quanta).
        self.mirror_deficit = [0] * self.CLIENTS
        self.prev_deficit = [0] * self.CLIENTS
        self.prev_cost = [1] * self.CLIENTS
        return completions

    def clear_scoreboard(self):
        self.served_cost = [0] * self.CLIENTS
        self.served_grants = [0] * self.CLIENTS

    # ------------------------------------------------------------------
    # Checks
    # ------------------------------------------------------------------

    def check_shares(self, active=None, tolerance=0.15, scenario=""):
        """Served-cost fractions must match quantum ratios within tolerance."""
        active = list(range(self.CLIENTS)) if active is None else list(active)
        total_served = sum(self.served_cost[i] for i in active)
        total_quanta = sum(self.quanta[i] for i in active)
        assert total_served > 0, f"{scenario}: nothing served"

        failures = []
        for i in active:
            expected = self.quanta[i] / total_quanta
            measured = self.served_cost[i] / total_served
            self.log.info(
                f"{scenario}: client {i} quantum={self.quanta[i]} "
                f"served_cost={self.served_cost[i]} grants={self.served_grants[i]} "
                f"share={measured:.3f} expected={expected:.3f}")
            if abs(measured - expected) > max(tolerance * expected, 0.02):
                failures.append(
                    f"client {i}: share {measured:.3f} vs expected "
                    f"{expected:.3f} (quantum {self.quanta[i]})")
        assert not failures, f"{scenario}: share check failed: {failures}"

    def check_mirror(self, scenario=""):
        assert not self.mirror_errors, (
            f"{scenario}: deficit discipline violations: "
            f"{self.mirror_errors[:5]} ({len(self.mirror_errors)} total)")

    # ------------------------------------------------------------------
    # Scenarios
    # ------------------------------------------------------------------

    async def scenario_equal_cost(self, completions, quanta=None):
        """Equal costs: DRR degenerates to WRR shares - the sanity anchor."""
        quanta = quanta or self._default_quanta()
        await self.set_quanta(quanta)
        self.clear_scoreboard()
        cost = min(2, self.MAX_COST)
        await self.run_traffic(completions, lambda i: cost)
        self.check_shares(scenario="equal_cost")
        self.check_mirror("equal_cost")

    async def scenario_mixed_costs(self, completions, quanta=None):
        """Per-frame random costs: shares must STILL follow quanta -
        this is the property the WRR does not have."""
        quanta = quanta or self._default_quanta()
        await self.set_quanta(quanta)
        self.clear_scoreboard()
        max_c = min(self.MAX_COST, self.MAX_QUANTUM)
        await self.run_traffic(
            completions, lambda i: random.randint(1, max_c))
        self.check_shares(scenario="mixed_costs")
        self.check_mirror("mixed_costs")

    async def scenario_cost_gt_quantum(self, completions):
        """A cost larger than one quantum takes several replenish rounds to
        save for - multi-round accumulation must serve it, share holds."""
        quanta = [2] * self.CLIENTS
        quanta[0] = 4
        await self.set_quanta(quanta)
        self.clear_scoreboard()
        big = min(self.MAX_COST, 3 * self.MAX_QUANTUM // 2)
        # client 1 asks for expensive frames on a small quantum
        await self.run_traffic(
            completions,
            lambda i: big if i == 1 else min(2, self.MAX_COST))
        assert self.served_grants[1] > 0, \
            "cost_gt_quantum: expensive client starved"
        self.check_shares(scenario="cost_gt_quantum", tolerance=0.20)
        self.check_mirror("cost_gt_quantum")

    async def scenario_disable(self, completions):
        """Quantum 0 disables a client completely."""
        quanta = self._default_quanta()
        quanta[self.CLIENTS - 1] = 0
        await self.set_quanta(quanta)
        self.clear_scoreboard()
        cost = min(2, self.MAX_COST)
        # the disabled client still REQUESTS - it must simply never win
        await self.run_traffic(completions, lambda i: cost)
        assert self.served_grants[self.CLIENTS - 1] == 0, \
            "disable: zero-quantum client was granted"
        self.check_shares(active=range(self.CLIENTS - 1), scenario="disable")
        self.check_mirror("disable")

    async def scenario_anti_hoarding(self, completions):
        """A client that sat idle must not bank deficit: run others, rejoin
        client 0, and require the discipline (mirror) to hold throughout -
        the mirror clears its deficit on request-drop exactly as the RTL
        must, so a hoarding RTL bug surfaces as an eligibility violation."""
        await self.set_quanta(self._default_quanta())
        self.clear_scoreboard()
        cost = min(2, self.MAX_COST)
        others = list(range(1, self.CLIENTS))
        await self.run_traffic(completions // 2, lambda i: cost, active=others)
        await self.run_traffic(completions, lambda i: cost)
        self.check_mirror("anti_hoarding")

    async def scenario_quantum_change(self, completions):
        """Change quanta mid-run: atomic FSM update, then shares follow the
        NEW ratio in the post-change window."""
        await self.set_quanta(self._default_quanta())
        self.clear_scoreboard()
        cost = min(2, self.MAX_COST)
        await self.run_traffic(completions // 2, lambda i: cost)

        flipped = list(reversed(self._default_quanta()))
        await self.set_quanta(flipped)   # waits out the FSM, clears mirror
        self.clear_scoreboard()
        await self.run_traffic(completions, lambda i: cost)
        self.check_shares(scenario="quantum_change(post)")
        self.check_mirror("quantum_change")

    def _default_quanta(self):
        """A ratio pattern that fits any CLIENTS count: [4,2,1,1,4,2,...]."""
        base = [4, 2, 1, 1]
        q = [base[i % 4] for i in range(self.CLIENTS)]
        return [min(v, self.MAX_QUANTUM - 1) for v in q]
