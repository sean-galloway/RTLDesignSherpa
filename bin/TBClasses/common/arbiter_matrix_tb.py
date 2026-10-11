# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ArbiterMatrixTB
# Purpose: Testbench for the matrix (distributed-state) fair arbiter.
#
# Documentation: cocotb-framework PyPI package
# Subsystem: framework
#
# Author: sean galloway
# Created: 2026-10-11

"""
Testbench for arbiter_matrix.

Proves the required arbiter properties with deterministic, self-checking
stimulus rather than relying on a randomized BFM:
  1. Grant is one-hot or zero and never granted to an unrequested client.
  2. Strong fairness: with all clients requesting continuously, each client is
     served exactly once per N consecutive grants.
  3. Fairness survives cold start and mid-stream idle gaps.
  4. A single requester is granted in the next cycle regardless of matrix state.
  5. Reset restores the documented initial order (client 0 wins first).
"""

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from TBClasses.shared.tbbase import TBBase


class ArbiterMatrixTB(TBBase):
    """Focused testbench for the matrix fair arbiter."""

    def __init__(self, dut):
        super().__init__(dut)

        self.CLIENTS = int(dut.CLIENTS)
        self.WAIT_GNT_ACK = int(dut.WAIT_GNT_ACK)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)

        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in ('gate', 'func', 'full'):
            self.TEST_LEVEL = 'gate'
        self.LEVEL_MULT = {'gate': 1, 'func': 2, 'full': 5}[self.TEST_LEVEL]

        self.log.info(
            f"ArbiterMatrixTB initialized: CLIENTS={self.CLIENTS}, "
            f"WAIT_GNT_ACK={self.WAIT_GNT_ACK}, TEST_LEVEL={self.TEST_LEVEL}, "
            f"SEED={self.SEED}"
        )

    # -------------------------------------------------------------------------
    # Lifecycle contract (/GLOBAL_REQUIREMENTS.md 2.2)
    # -------------------------------------------------------------------------
    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    async def setup_clocks_and_reset(self):
        await self.start_clock('clk', 10, units='ns')
        await self.reset_dut()

    async def reset_dut(self):
        self.dut.rst_n.value = 0
        self.dut.request.value = 0
        self.dut.block_arb.value = 0
        if self.CLIENTS > 1:
            self.dut.grant_ack.value = 0
        for _ in range(10):
            await RisingEdge(self.dut.clk)
        self.dut.rst_n.value = 1
        for _ in range(2):
            await RisingEdge(self.dut.clk)
        await Timer(1, units='ns')

    async def wait_clocks(self, num_clocks: int):
        for _ in range(num_clocks):
            await RisingEdge(self.dut.clk)
        await Timer(1, units='ns')

    def get_time_ns_str(self):
        return f" @ {get_sim_time('ns'):.1f}ns"

    # -------------------------------------------------------------------------
    # Low-level helpers
    # -------------------------------------------------------------------------
    async def set_request(self, value: int):
        self.dut.request.value = value
        await self.wait_clocks(1)

    def read_grant(self):
        gv = int(self.dut.grant_valid.value)
        gnt = int(self.dut.grant.value)
        gid = int(self.dut.grant_id.value) if self.CLIENTS > 1 else 0
        return gv, gnt, gid

    def is_one_hot(self, value: int) -> bool:
        return value == 0 or ((value & (value - 1)) == 0)

    def one_hot_to_id(self, value: int) -> int:
        if value == 0:
            return 0
        return (value.bit_length() - 1)

    # -------------------------------------------------------------------------
    # Required tests
    # -------------------------------------------------------------------------
    async def test_one_hot_and_request_match(self):
        """Grant is one-hot or zero and only grants a requesting client."""
        self.log.info(f"=== one-hot / request-match test ==={self.get_time_ns_str()}")

        # Exhaustive for small N, strided random for larger N.
        if self.CLIENTS <= 5:
            patterns = list(range(1 << self.CLIENTS))
        else:
            patterns = [0, (1 << self.CLIENTS) - 1]
            rng = random.Random(self.SEED)
            for _ in range(50 * self.LEVEL_MULT):
                patterns.append(rng.randint(0, (1 << self.CLIENTS) - 1))

        for req in patterns:
            await self.set_request(req)
            gv, gnt, gid = self.read_grant()

            assert self.is_one_hot(gnt), (
                f"req=0x{req:x}: grant=0x{gnt:x} is not one-hot or zero"
            )
            if gv:
                assert gnt != 0, f"req=0x{req:x}: grant_valid=1 but grant=0"
                assert (gnt & req) == gnt, (
                    f"req=0x{req:x}: grant=0x{gnt:x} grants an unrequested client"
                )
                assert gid == self.one_hot_to_id(gnt), (
                    f"req=0x{req:x}: grant_id={gid} does not match grant=0x{gnt:x}"
                )
            else:
                assert gnt == 0, (
                    f"req=0x{req:x}: grant_valid=0 but grant=0x{gnt:x}"
                )

        self.log.info("one-hot / request-match test PASSED")
        return True

    async def test_strong_fairness_continuous(self):
        """All clients requesting: each grants exactly once per N grants."""
        self.log.info(
            f"=== strong fairness (continuous) test ==={self.get_time_ns_str()}"
        )

        await self.set_request((1 << self.CLIENTS) - 1)

        # Wait for the first grant to appear (registered output).
        for _ in range(self.CLIENTS + 5):
            gv, _, _ = self.read_grant()
            if gv:
                break
            await self.wait_clocks(1)
        assert gv == 1, "No grant appeared with all clients requesting"

        # Count 4N consecutive grants.
        window = 4 * self.CLIENTS
        counts = [0] * self.CLIENTS
        for _ in range(window):
            await self.wait_clocks(1)
            gv, gnt, gid = self.read_grant()
            assert gv == 1, (
                f"grant_valid dropped with all clients requesting "
                f"(cycle {_} of {window})"
            )
            winner = self.one_hot_to_id(gnt)
            assert winner == gid, (
                f"grant_id={gid} mismatches grant=0x{gnt:x}"
            )
            counts[winner] += 1

        self.log.info(f"grant counts over {window} cycles: {counts}")
        expected = window // self.CLIENTS
        for c in range(self.CLIENTS):
            assert counts[c] == expected, (
                f"client {c} got {counts[c]} grants, expected {expected} "
                f"over {window} consecutive grants"
            )

        self.log.info("strong fairness (continuous) test PASSED")
        return True

    async def test_fairness_cold_start_and_gaps(self):
        """Rotation is correct from reset and after partial-request gaps."""
        self.log.info(
            f"=== fairness cold-start + gaps test ==={self.get_time_ns_str()}"
        )

        # Cold start: all request, expect 0,1,2,...,N-1,0,...
        await self.reset_dut()
        self.dut.request.value = (1 << self.CLIENTS) - 1

        expected = list(range(self.CLIENTS)) + list(range(self.CLIENTS))
        observed = []
        for _ in range(2 * self.CLIENTS):
            await self.wait_clocks(1)
            gv, gnt, _ = self.read_grant()
            assert gv == 1, "grant_valid dropped during cold-start rotation"
            observed.append(self.one_hot_to_id(gnt))
        assert observed == expected, (
            f"cold-start rotation {observed} != expected {expected}"
        )
        self.log.info(f"cold-start rotation: {observed}")

        # Mid-stream gap: drop clients above 0 for N cycles, then restore all.
        # The matrix continues to rotate among the requesting subset, and when
        # all are restored the order resumes from the new head.
        self.dut.request.value = 0b0001  # only client 0
        await self.wait_clocks(self.CLIENTS)

        # Now bring all back and capture the next N grants.
        self.dut.request.value = (1 << self.CLIENTS) - 1
        after_gap = []
        for _ in range(self.CLIENTS):
            await self.wait_clocks(1)
            gv, gnt, _ = self.read_grant()
            assert gv == 1, "grant_valid dropped after gap"
            after_gap.append(self.one_hot_to_id(gnt))

        # Each client appears exactly once in the N grants after the gap.
        assert sorted(after_gap) == list(range(self.CLIENTS)), (
            f"post-gap rotation {after_gap} is not a permutation of all clients"
        )
        self.log.info(f"post-gap rotation: {after_gap}")

        self.log.info("fairness cold-start + gaps test PASSED")
        return True

    async def test_single_requester_immediate(self):
        """A lone requester is granted in one cycle regardless of matrix state."""
        self.log.info(
            f"=== single requester immediacy test ==={self.get_time_ns_str()}"
        )

        # Scramble the matrix first with some traffic.
        rng = random.Random(self.SEED)
        for _ in range(self.CLIENTS * 3):
            req = rng.randint(1, (1 << self.CLIENTS) - 1)
            await self.set_request(req)

        # Now request one client at a time and verify immediate service.
        for client in range(self.CLIENTS):
            await self.set_request(1 << client)
            gv, gnt, gid = self.read_grant()
            assert gv == 1, (
                f"client {client} alone: no grant (grant_valid={gv})"
            )
            assert gnt == (1 << client), (
                f"client {client} alone: grant=0x{gnt:x}, expected 0x{(1 << client):x}"
            )
            assert gid == client, (
                f"client {client} alone: grant_id={gid}, expected {client}"
            )

        self.log.info("single requester immediacy test PASSED")
        return True

    async def test_reset_order(self):
        """Reset restores client 0 as the highest-priority requester."""
        self.log.info(f"=== reset-order test ==={self.get_time_ns_str()}")

        # Scramble state.
        rng = random.Random(self.SEED)
        for _ in range(self.CLIENTS * 4):
            req = rng.randint(1, (1 << self.CLIENTS) - 1)
            await self.set_request(req)

        # Reset and request all clients.
        await self.reset_dut()
        await self.set_request((1 << self.CLIENTS) - 1)

        gv, gnt, gid = self.read_grant()
        assert gv == 1, "No grant after reset with all clients requesting"
        assert gnt == 1, (
            f"first grant after reset is 0x{gnt:x}, expected 0x1 (client 0)"
        )
        assert gid == 0, f"first grant_id after reset is {gid}, expected 0"

        self.log.info("reset-order test PASSED")
        return True

    async def test_block_arb(self):
        """block_arb forces no grants."""
        self.log.info(f"=== block_arb test ==={self.get_time_ns_str()}")

        await self.set_request((1 << self.CLIENTS) - 1)
        await self.wait_clocks(2)
        self.dut.block_arb.value = 1
        await self.wait_clocks(3)

        gv, gnt, _ = self.read_grant()
        assert gv == 0 and gnt == 0, (
            f"block_arb high but grant_valid={gv}, grant=0x{gnt:x}"
        )

        self.dut.block_arb.value = 0
        await self.wait_clocks(2)
        gv, gnt, gid = self.read_grant()
        assert gv == 1, "grant did not resume after block_arb release"
        assert (gnt & ((1 << self.CLIENTS) - 1)) != 0, "grant is zero after resume"

        self.log.info("block_arb test PASSED")
        return True

    async def run_all_tests(self):
        """Run the matrix arbiter test suite."""
        results = []

        results.append(("one-hot/request-match",
                        await self.test_one_hot_and_request_match()))
        results.append(("strong-fairness-continuous",
                        await self.test_strong_fairness_continuous()))
        results.append(("fairness-cold-start-and-gaps",
                        await self.test_fairness_cold_start_and_gaps()))
        results.append(("single-requester-immediate",
                        await self.test_single_requester_immediate()))
        results.append(("reset-order",
                        await self.test_reset_order()))
        results.append(("block-arb",
                        await self.test_block_arb()))

        self.log.info("=" * 60)
        self.log.info("ArbiterMatrix test summary:")
        all_passed = True
        for name, passed in results:
            status = "PASSED" if passed else "FAILED"
            self.log.info(f"  {name}: {status}")
            all_passed = all_passed and passed
        self.log.info("=" * 60)

        return all_passed
