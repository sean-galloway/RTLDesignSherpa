# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ArbiterMatrixWeightedTB
# Purpose: Testbench for the weighted matrix arbiter.
#
# Documentation: cocotb-framework PyPI package
# Subsystem: framework
#
# Author: sean galloway
# Created: 2026-10-11

"""
Testbench for arbiter_matrix_weighted.

Proves weighted, strong-fairness arbitration with deferred matrix rotation:
  1. Weighted grant sequences match the documented credit-based scheduling.
  2. Grant is one-hot or zero and only granted to a requesting, credit-eligible
     client.
  3. A weight=0 client is never granted.
  4. Dynamic weight changes take effect at the next credit reload.
  5. ACK mode hold, foreign-ack immunity, same-cycle handoff, and single-
     requester re-grant behave like the base matrix arbiter.
  6. Rotation remains correct after idle gaps and across parameter sweeps.
"""

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from TBClasses.shared.tbbase import TBBase


class ArbiterMatrixWeightedTB(TBBase):
    """Focused testbench for the weighted matrix arbiter."""

    def __init__(self, dut):
        super().__init__(dut)

        self.CLIENTS = int(dut.CLIENTS)
        self.WAIT_GNT_ACK = int(dut.WAIT_GNT_ACK)
        self.MAX_LEVELS = int(dut.MAX_LEVELS)

        if hasattr(dut, 'MAX_LEVELS_WIDTH'):
            try:
                self.MAX_LEVELS_WIDTH = int(dut.MAX_LEVELS_WIDTH.value)
            except Exception:
                self.MAX_LEVELS_WIDTH = int(dut.MAX_LEVELS_WIDTH)
        else:
            self.MAX_LEVELS_WIDTH = (self.MAX_LEVELS - 1).bit_length()

        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)

        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in ('gate', 'func', 'full'):
            self.TEST_LEVEL = 'gate'
        self.LEVEL_MULT = {'gate': 1, 'func': 2, 'full': 5}[self.TEST_LEVEL]

        self.log.info(
            f"ArbiterMatrixWeightedTB initialized: CLIENTS={self.CLIENTS}, "
            f"MAX_LEVELS={self.MAX_LEVELS}, WAIT_GNT_ACK={self.WAIT_GNT_ACK}, "
            f"TEST_LEVEL={self.TEST_LEVEL}, SEED={self.SEED}"
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
        self.dut.max_thresh.value = 0
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
    def set_weights(self, weights):
        """Pack per-client weights into the max_thresh vector."""
        if len(weights) != self.CLIENTS:
            raise ValueError(
                f"weights length {len(weights)} != CLIENTS {self.CLIENTS}"
            )
        packed = 0
        for i, w in enumerate(weights):
            packed |= (int(w) & ((1 << self.MAX_LEVELS_WIDTH) - 1)) << (i * self.MAX_LEVELS_WIDTH)
        self.dut.max_thresh.value = packed

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
    async def test_weighted_sequence(self):
        """Verify the documented consecutive-grant weight sequence."""
        self.log.info(f"=== weighted sequence test ==={self.get_time_ns_str()}")

        if self.CLIENTS == 3:
            weights = [3, 1, 2]
            expected_period = [0, 0, 0, 1, 2, 2]
        elif self.CLIENTS == 2:
            weights = [2, 1]
            expected_period = [0, 0, 1]
        elif self.CLIENTS == 4:
            weights = [3, 1, 2, 1]
            expected_period = [0, 0, 0, 1, 2, 2, 3]
        elif self.CLIENTS == 5:
            weights = [3, 1, 2, 1, 1]
            expected_period = [0, 0, 0, 1, 2, 2, 3, 4]
        elif self.CLIENTS == 8:
            weights = [3, 1, 2, 1, 1, 1, 1, 1]
            expected_period = [0, 0, 0, 1, 2, 2, 3, 4, 5, 6, 7]
        else:
            # Fall back to a simple 2:1:... pattern and check ratios rather
            # than an exact sequence.
            weights = [2] + [1] * (self.CLIENTS - 1)
            expected_period = None

        self.set_weights(weights)
        await self.wait_clocks(3)  # load credits

        await self.set_request((1 << self.CLIENTS) - 1)

        if expected_period is not None:
            periods = 2 + self.LEVEL_MULT
            expected = expected_period * periods
            observed = []
            for _ in range(len(expected)):
                gv, gnt, gid = self.read_grant()
                assert gv == 1, (
                    f"grant_valid dropped with all clients requesting "
                    f"(observed={observed})"
                )
                winner = self.one_hot_to_id(gnt)
                assert winner == gid, (
                    f"grant_id={gid} mismatches grant=0x{gnt:x}"
                )
                observed.append(winner)
                await self.wait_clocks(1)

            self.log.info(f"observed sequence: {observed[:len(expected_period)*2]}")
            assert observed == expected, (
                f"weighted sequence mismatch\nobserved: {observed}\n"
                f"expected: {expected}"
            )
        else:
            # Ratio check: client 0 should get roughly twice as many grants as
            # every other non-zero client.
            cycles = (sum(weights) * self.CLIENTS * 2) * self.LEVEL_MULT
            counts = [0] * self.CLIENTS
            for _ in range(cycles):
                gv, gnt, gid = self.read_grant()
                assert gv == 1, "grant_valid dropped with all clients requesting"
                counts[self.one_hot_to_id(gnt)] += 1
                await self.wait_clocks(1)
            self.log.info(f"ratio counts: {counts}")
            assert counts[0] > 0
            for c in range(1, self.CLIENTS):
                assert counts[c] > 0
                ratio = counts[0] / counts[c]
                assert 1.5 < ratio < 2.5, (
                    f"client 0 / client {c} ratio {ratio} out of range"
                )

        self.log.info("weighted sequence test PASSED")
        return True

    async def test_one_hot_and_request_match(self):
        """Grant is one-hot or zero and only grants an eligible client."""
        self.log.info(f"=== one-hot / request-match test ==={self.get_time_ns_str()}")

        # Equal weights of 2 give every client credits.
        self.set_weights([2] * self.CLIENTS)
        await self.wait_clocks(3)

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

    async def test_zero_weight(self):
        """A weight=0 client is never granted."""
        self.log.info(f"=== zero-weight test ==={self.get_time_ns_str()}")

        if self.CLIENTS < 2:
            self.log.info("zero-weight test skipped for single client")
            return True

        weights = [2] * self.CLIENTS
        zero_client = 1
        weights[zero_client] = 0
        self.set_weights(weights)
        await self.wait_clocks(3)

        await self.set_request((1 << self.CLIENTS) - 1)

        window = sum(w for w in weights) * 4 * self.LEVEL_MULT
        for _ in range(window):
            gv, gnt, gid = self.read_grant()
            assert gv == 1, "grant_valid dropped with all clients requesting"
            winner = self.one_hot_to_id(gnt)
            assert winner != zero_client, (
                f"client {zero_client} (weight=0) was granted"
            )
            await self.wait_clocks(1)

        self.log.info("zero-weight test PASSED")
        return True

    async def test_weight_change(self):
        """Dynamic weight changes take effect at the next credit reload."""
        self.log.info(f"=== weight-change test ==={self.get_time_ns_str()}")

        # Start with client 0 weight 2; after it exhausts its two credits we
        # drop it to weight 1.  The very next turn for client 0 must then be a
        # single grant, confirming the new weight loaded at the reload point.
        self.set_weights([2] + [1] * (self.CLIENTS - 1))
        await self.wait_clocks(3)
        await self.set_request((1 << self.CLIENTS) - 1)

        # Warm up until we have seen at least one full rotation.
        for _ in range(self.CLIENTS * 4):
            await self.wait_clocks(1)

        # Change client 0 to weight 1.  It may still have one leftover credit
        # from its previous weight-2 turn, so observe until we find a client-0
        # grant whose next client-0 grant is separated by every other client.
        new_weights = [1] + [1] * (self.CLIENTS - 1)
        self.set_weights(new_weights)
        self.log.info(f"changed weights to {new_weights}{self.get_time_ns_str()}")

        post_change = []
        found_proper_spacing = False
        max_cycles = self.CLIENTS * 12 * self.LEVEL_MULT
        cycles = 0
        while cycles < max_cycles:
            gv, gnt, _ = self.read_grant()
            assert gv == 1
            winner = self.one_hot_to_id(gnt)
            post_change.append(winner)
            cycles += 1

            # Check spacing every time client 0 is granted (except the first).
            if winner == 0 and post_change.count(0) >= 2:
                # Find the previous client-0 grant.
                last = len(post_change) - 1
                prev = last - 1 - post_change[-2::-1].index(0)
                between = set(post_change[prev + 1:last])
                expected_between = set(range(1, self.CLIENTS))
                if between == expected_between:
                    found_proper_spacing = True
                    break
            await self.wait_clocks(1)

        assert found_proper_spacing, (
            f"client 0 never showed weight-1 spacing after change; "
            f"post_change={post_change}"
        )

        self.log.info("weight-change test PASSED")
        return True

    async def test_idle_gap(self):
        """Rotation is correct after a mid-stream idle gap."""
        self.log.info(f"=== idle-gap test ==={self.get_time_ns_str()}")

        # Use weight 1 so the matrix rotates every grant; then the first CLIENTS
        # grants after the gap are guaranteed to be a permutation.
        self.set_weights([1] * self.CLIENTS)
        await self.wait_clocks(3)
        await self.set_request((1 << self.CLIENTS) - 1)

        # Run a few grants to put the matrix in a non-trivial state.
        for _ in range(self.CLIENTS * 2):
            await self.wait_clocks(1)

        # Drop all clients above 0 for several cycles.
        self.dut.request.value = 0b0001
        await self.wait_clocks(self.CLIENTS * 2)

        # Restore all clients; the next CLIENTS grants must be a permutation.
        self.dut.request.value = (1 << self.CLIENTS) - 1
        after_gap = []
        for _ in range(self.CLIENTS):
            await self.wait_clocks(1)
            gv, gnt, _ = self.read_grant()
            assert gv == 1, "grant_valid dropped after idle gap"
            after_gap.append(self.one_hot_to_id(gnt))

        assert sorted(after_gap) == list(range(self.CLIENTS)), (
            f"post-gap rotation {after_gap} is not a permutation of all clients"
        )
        self.log.info(f"post-gap rotation: {after_gap}")

        self.log.info("idle-gap test PASSED")
        return True

    async def test_single_requester_immediate(self):
        """A lone requester is granted in one cycle regardless of matrix state."""
        self.log.info(f"=== single requester immediacy test ==={self.get_time_ns_str()}")

        self.set_weights([2] * self.CLIENTS)
        await self.wait_clocks(3)

        rng = random.Random(self.SEED)
        for _ in range(self.CLIENTS * 3):
            req = rng.randint(1, (1 << self.CLIENTS) - 1)
            await self.set_request(req)

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

        self.set_weights([2] * self.CLIENTS)
        await self.wait_clocks(3)

        rng = random.Random(self.SEED)
        for _ in range(self.CLIENTS * 4):
            req = rng.randint(1, (1 << self.CLIENTS) - 1)
            await self.set_request(req)

        await self.reset_dut()
        self.set_weights([2] * self.CLIENTS)
        await self.wait_clocks(3)
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

        self.set_weights([2] * self.CLIENTS)
        await self.wait_clocks(3)
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

    # -------------------------------------------------------------------------
    # ACK-mode directed tests
    # -------------------------------------------------------------------------
    async def _wait_for_grant(self, timeout=20):
        for _ in range(timeout):
            gv, gnt, gid = self.read_grant()
            if gv:
                return gv, gnt, gid
            await self.wait_clocks(1)
        raise AssertionError(f"No grant appeared within {timeout} cycles")

    async def _drive_ack(self, ack_vec: int, cycles: int = 1):
        if self.CLIENTS > 1:
            self.dut.grant_ack.value = ack_vec
        await self.wait_clocks(cycles)
        if self.CLIENTS > 1:
            self.dut.grant_ack.value = 0

    async def test_ack_hold_until_owner_ack(self):
        """In ACK mode the grant is held until the winner acknowledges it."""
        if self.WAIT_GNT_ACK != 1:
            self.log.info("ACK hold test skipped in no-ACK mode")
            return True

        self.log.info(f"=== ACK hold-until-owner-ack test ==={self.get_time_ns_str()}")

        # Use weight 1 so a single ACK exhausts the winner and forces rotation.
        self.set_weights([1] * self.CLIENTS)
        await self.reset_dut()
        self.set_weights([1] * self.CLIENTS)
        await self.wait_clocks(3)
        self.dut.request.value = (1 << self.CLIENTS) - 1
        await self.wait_clocks(1)

        _, gnt, gid = await self._wait_for_grant()
        first_winner = gid
        self.log.info(f"first grant to client {first_winner}")

        self.dut.grant_ack.value = 0
        for _ in range(5):
            await self.wait_clocks(1)
            gv, held_gnt, held_gid = self.read_grant()
            assert gv == 1, "grant_valid dropped while waiting for ACK"
            assert held_gid == first_winner, (
                f"grant changed from {first_winner} to {held_gid} before ACK"
            )
            assert held_gnt == gnt, (
                f"grant vector changed from 0x{gnt:x} to 0x{held_gnt:x} before ACK"
            )

        await self._drive_ack(1 << first_winner, 1)
        await self.wait_clocks(1)
        gv, next_gnt, next_gid = self.read_grant()
        if self.CLIENTS > 1:
            assert gv == 1, "no next grant after owner ACK with pending requests"
            assert next_gid != first_winner, (
                f"grant did not rotate after ACK (still {next_gid})"
            )
            assert (next_gnt & ((1 << self.CLIENTS) - 1)) != 0, "next grant is zero"

        self.log.info("ACK hold-until-owner-ack test PASSED")
        return True

    async def test_ack_foreign_ack_immunity(self):
        """Only the currently granted client's ACK bit retires the held grant."""
        if self.WAIT_GNT_ACK != 1:
            self.log.info("foreign-ACK immunity test skipped in no-ACK mode")
            return True
        if self.CLIENTS < 2:
            self.log.info("foreign-ACK immunity test skipped for single client")
            return True

        self.log.info(f"=== ACK foreign-ack immunity test ==={self.get_time_ns_str()}")

        # Use weight 1 so the owner ACK exhausts the winner and forces rotation.
        self.set_weights([1] * self.CLIENTS)
        await self.reset_dut()
        self.set_weights([1] * self.CLIENTS)
        await self.wait_clocks(3)
        self.dut.request.value = (1 << self.CLIENTS) - 1
        await self.wait_clocks(1)

        _, _, first_gid = await self._wait_for_grant()
        foreign = (first_gid + 1) % self.CLIENTS
        self.log.info(f"first grant to client {first_gid}; foreign client {foreign}")

        self.dut.grant_ack.value = 1 << foreign
        for _ in range(5):
            await self.wait_clocks(1)
            gv, _, gid = self.read_grant()
            assert gv == 1, "grant_valid dropped after foreign ACK"
            assert gid == first_gid, (
                f"foreign ACK changed grant from {first_gid} to {gid}"
            )

        await self._drive_ack(1 << first_gid, 1)
        await self.wait_clocks(1)
        gv, _, gid = self.read_grant()
        assert gv == 1, "no next grant after owner ACK"
        assert gid != first_gid, "grant did not rotate after owner ACK"

        self.log.info("ACK foreign-ack immunity test PASSED")
        return True

    async def test_ack_back_to_back_handoff(self):
        """ACK-mode grants hand off in consecutive cycles with no bubble."""
        if self.WAIT_GNT_ACK != 1:
            self.log.info("back-to-back handoff test skipped in no-ACK mode")
            return True
        if self.CLIENTS < 2:
            self.log.info("back-to-back handoff test skipped for single client")
            return True

        self.log.info(f"=== ACK back-to-back handoff test ==={self.get_time_ns_str()}")

        # Weight 1 everywhere so every ACK causes a rotation.
        self.set_weights([1] * self.CLIENTS)
        await self.reset_dut()
        self.set_weights([1] * self.CLIENTS)
        await self.wait_clocks(3)
        self.dut.request.value = (1 << self.CLIENTS) - 1
        await self.wait_clocks(1)

        expected = list(range(self.CLIENTS)) + list(range(self.CLIENTS))
        observed = []

        _, _, gid = await self._wait_for_grant()
        observed.append(gid)
        for _ in range(2 * self.CLIENTS - 1):
            await self._drive_ack(1 << gid, 1)
            await self.wait_clocks(1)
            gv, _, gid = self.read_grant()
            assert gv == 1, "grant_valid dropped during back-to-back handoff"
            observed.append(gid)

        assert observed == expected, (
            f"back-to-back rotation {observed} != expected {expected}"
        )
        self.log.info(f"back-to-back rotation: {observed}")

        self.log.info("ACK back-to-back handoff test PASSED")
        return True

    async def test_ack_single_requester(self):
        """A lone requester in ACK mode is re-granted after each ACK."""
        if self.WAIT_GNT_ACK != 1:
            self.log.info("single-requester ACK test skipped in no-ACK mode")
            return True

        self.log.info(f"=== ACK single-requester test ==={self.get_time_ns_str()}")

        self.set_weights([2] * self.CLIENTS)
        for client in range(self.CLIENTS):
            await self.reset_dut()
            self.set_weights([2] * self.CLIENTS)
            await self.wait_clocks(3)
            self.dut.request.value = 1 << client
            await self.wait_clocks(1)

            for rep in range(3):
                gv, gnt, gid = await self._wait_for_grant()
                assert gid == client, (
                    f"client {client} rep {rep}: grant_id={gid}"
                )
                assert gnt == (1 << client), (
                    f"client {client} rep {rep}: grant=0x{gnt:x}"
                )
                await self._drive_ack(1 << client, 1)
                await self.wait_clocks(1)

        self.log.info("ACK single-requester test PASSED")
        return True

    async def run_all_tests(self):
        """Run the weighted matrix arbiter test suite."""
        results = []

        if self.WAIT_GNT_ACK == 0:
            results.append(("weighted-sequence",
                            await self.test_weighted_sequence()))
            results.append(("one-hot/request-match",
                            await self.test_one_hot_and_request_match()))
            results.append(("zero-weight",
                            await self.test_zero_weight()))
            results.append(("weight-change",
                            await self.test_weight_change()))
            results.append(("idle-gap",
                            await self.test_idle_gap()))
            results.append(("single-requester-immediate",
                            await self.test_single_requester_immediate()))
            results.append(("reset-order",
                            await self.test_reset_order()))
            results.append(("block-arb",
                            await self.test_block_arb()))
        else:
            results.append(("reset-order",
                            await self.test_reset_order()))

        results.append(("ack-hold-until-owner-ack",
                        await self.test_ack_hold_until_owner_ack()))
        results.append(("ack-foreign-ack-immunity",
                        await self.test_ack_foreign_ack_immunity()))
        results.append(("ack-back-to-back-handoff",
                        await self.test_ack_back_to_back_handoff()))
        results.append(("ack-single-requester",
                        await self.test_ack_single_requester()))

        self.log.info("=" * 60)
        self.log.info("ArbiterMatrixWeighted test summary:")
        all_passed = True
        for name, passed in results:
            status = "PASSED" if passed else "FAILED"
            self.log.info(f"  {name}: {status}")
            all_passed = all_passed and passed
        self.log.info("=" * 60)

        return all_passed
