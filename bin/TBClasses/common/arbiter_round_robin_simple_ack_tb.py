# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ArbiterRoundRobinSimpleAckTB
# Purpose: Simple Round Robin Testbench with grant/ack handshake
#
# Documentation: cocotb-framework PyPI package
# Subsystem: framework
#
# Author: sean galloway
# Created: 2026-10-04

"""
Simple Round Robin Testbench with grant/ack handshake

ArbiterRoundRobinSimpleTB in ACK mode (WAIT_GNT_ACK=1, the same switch the WRR TB
uses), plus directed checks of the handshake itself -- hold-until-ACK, foreign
ACKs ignored, same-cycle ACK hands off back-to-back -- that master-driven traffic
cannot pin down.
"""

import random
from cocotb.triggers import FallingEdge

from TBClasses.common.arbiter_round_robin_simple_tb import ArbiterRoundRobinSimpleTB


class ArbiterRoundRobinSimpleAckTB(ArbiterRoundRobinSimpleTB):
    """Simple Round Robin Arbiter Testbench, ACK mode"""

    WAIT_GNT_ACK = 1

    def __init__(self, dut):
        super().__init__(dut)
        self.ALL_MASK = (1 << self.CLIENTS) - 1
        # Stray (non-owner) ACK rising edges this TB drives on purpose. The
        # compliance verdict must report exactly this many 'unexpected_ack'.
        self._injected_stray_acks = 0

    # =============================================================================
    # HANDSHAKE HELPERS
    # =============================================================================

    async def take_manual_control(self):
        """Stop the master (it owns request/grant_ack) and leave the DUT idle."""
        await self.master.drain_and_idle(idle_cycles=10)
        await self.master.shutdown()
        self.dut.request.value = 0
        self.dut.grant_ack.value = 0
        await self.wait_clocks('clk', 5)
        assert int(self.dut.grant_valid.value) == 0, "Grant still held after drain"

    async def release_manual_control(self):
        """Hand request/grant_ack back to the master."""
        self.dut.request.value = 0
        self.dut.grant_ack.value = 0
        await self.wait_clocks('clk', 5)
        await self.master.startup()

    async def _wait_grant_for(self, client_id: int, timeout_cycles: int = 10) -> int:
        """Sample at falling edges until client_id holds the grant; return cycles waited."""
        for cycle in range(timeout_cycles):
            await FallingEdge(self.dut.clk)
            if int(self.dut.grant_valid.value) and int(self.dut.grant.value) == (1 << client_id):
                return cycle
        raise AssertionError(f"Client {client_id} not granted within {timeout_cycles} cycles")

    # =============================================================================
    # DIRECTED HANDSHAKE TESTS (master stopped, signals driven directly)
    # =============================================================================

    async def test_grant_held_until_ack(self):
        """Grant must stay put until the OWNER acks -- even with the request
        dropped and every other client's ACK bit toggling."""
        self.log.info(f"Starting grant-held-until-ack test{self.get_time_ns_str()}")
        await self.take_manual_control()

        hold_cycles = 6 * self.LEVEL_MULT
        for client_id in range(self.CLIENTS):
            owner = 1 << client_id
            self.dut.request.value = owner
            waited = await self._wait_grant_for(client_id)
            # Registered grant: visible the cycle after the request is sampled.
            assert waited <= 1, f"Client {client_id}: grant took {waited} cycles (expected <= 1)"

            # Request dropped: grant must still be held. Foreign ACKs must not retire it.
            self.dut.request.value = 0
            prev_stray = 0
            for k in range(hold_cycles):
                stray = random.randint(0, self.ALL_MASK) & ~owner
                # The monitor reports a stray bit once per rising edge, not per
                # cycle it stays high -- count what it should see.
                self._injected_stray_acks += (stray & ~prev_stray).bit_count()
                prev_stray = stray
                self.dut.grant_ack.value = stray
                await FallingEdge(self.dut.clk)
                assert int(self.dut.grant_valid.value) == 1, (
                    f"Client {client_id}: grant_valid dropped at hold cycle {k} without an ACK")
                assert int(self.dut.grant.value) == owner, (
                    f"Client {client_id}: grant moved to {int(self.dut.grant.value):#x} at hold "
                    f"cycle {k} without the owner's ACK (foreign ACKs must be ignored)")
                assert int(self.dut.grant_id.value) == client_id, (
                    f"Client {client_id}: grant_id {int(self.dut.grant_id.value)} while held")

            # Owner ACK with nothing else requesting retires the grant.
            self.dut.grant_ack.value = owner
            await FallingEdge(self.dut.clk)
            self.dut.grant_ack.value = 0
            assert int(self.dut.grant_valid.value) == 0, (
                f"Client {client_id}: grant still valid after owner ACK with no requests")
            await self.wait_clocks('clk', 2)

        await self.release_manual_control()
        self.log.info(f"Grant-held-until-ack test passed{self.get_time_ns_str()}")

    async def test_back_to_back_handoff(self):
        """All clients requesting, owner acks the same cycle: the next client in
        rotation must be granted the very next cycle -- no idle bubble, no skips."""
        self.log.info(f"Starting back-to-back handoff test{self.get_time_ns_str()}")
        await self.take_manual_control()

        self.dut.request.value = self.ALL_MASK
        for _ in range(3):  # first grant registers one cycle after the request
            await FallingEdge(self.dut.clk)
            if int(self.dut.grant_valid.value):
                break
        sequence = []
        for k in range(3 * self.CLIENTS):
            if k:
                await FallingEdge(self.dut.clk)
            assert int(self.dut.grant_valid.value) == 1, (
                f"Idle bubble at handoff {k}: grant_valid low while all clients request. "
                f"Sequence so far: {sequence}")
            gid = int(self.dut.grant_id.value)
            assert int(self.dut.grant.value) == (1 << gid), (
                f"grant {int(self.dut.grant.value):#x} disagrees with grant_id {gid}")
            if sequence:
                expected = (sequence[-1] + 1) % self.CLIENTS
                assert gid == expected, (
                    f"Rotation broken at handoff {k}: granted {gid}, expected {expected}. "
                    f"Sequence: {sequence + [gid]}")
            sequence.append(gid)
            self.dut.grant_ack.value = 1 << gid   # same-cycle ACK from the owner

        # Retire the last grant before handing back.
        await FallingEdge(self.dut.clk)
        self.dut.request.value = 0
        self.dut.grant_ack.value = int(self.dut.grant.value)
        await FallingEdge(self.dut.clk)
        self.dut.grant_ack.value = 0
        self.log.info(f"Back-to-back sequence: {sequence}")

        await self.release_manual_control()
        self.log.info(f"Back-to-back handoff test passed{self.get_time_ns_str()}")
