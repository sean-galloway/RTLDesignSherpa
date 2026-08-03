# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: MonbusArbiterGrantHoldTB
# Purpose: Testbench for monbus_arbiter_grant_hold
# Subsystem: framework
#
# Extracted from val/amba/test_monbus_arbiter_grant_hold.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
from cocotb.triggers import RisingEdge, FallingEdge
from TBClasses.shared.tbbase import TBBase


class MonbusArbiterGrantHoldTB(TBBase):
    """Minimal driver/checker for the monbus_arbiter grant-hold contract.

    The arbiter's client-side ports are SystemVerilog unpacked arrays
    (`monbus_valid_in [CLIENTS]`), so they are driven by index rather than
    through a packed-bus BFM.
    """

    def __init__(self, dut):
        super().__init__(dut)
        self.CLIENTS = int(os.environ.get('TEST_CLIENTS', '4'))
        self.PKT_W = 128   # MONBUS_PKT_WIDTH
        self.TS_W = 64     # MONBUS_TS_WIDTH
        self.clk_name = 'axi_aclk'
        self.axi_aclk = dut.axi_aclk
        self.rst_n = dut.axi_aresetn
        # per-client transfer counters
        self.xfers = [0] * self.CLIENTS
        # contract violation counters
        self.grant_rotations_without_xfer = 0
        self.stability_violations = 0

    # ---- MANDATORY three methods -----------------------------------------

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    # ---- stimulus ---------------------------------------------------------

    async def initialize(self):
        """Idle all client inputs and give each client a unique payload."""
        self.dut.block_arb.value = 0
        self.dut.monbus_ready.value = 0
        self.dut.monbus_valid_in.value = 0
        # unique, easily-identified payload per client, packed side by side
        pkt = 0
        ts = 0
        for i in range(self.CLIENTS):
            pkt |= (i + 1) << (i * self.PKT_W)
            ts |= (i + 1) << (i * self.TS_W)
        self.dut.monbus_packet_in.value = pkt
        self.dut.monbus_timestamp_in.value = ts
        await self.wait_clocks(self.clk_name, 1)

    def request(self, clients):
        """Assert monbus_valid_in for the given client indices, clear others."""
        vec = 0
        for i in clients:
            vec |= (1 << i)
        self.dut.monbus_valid_in.value = vec

    def _grant_vector(self):
        return int(self.dut.grant.value)

    # ---- monitors ---------------------------------------------------------

    async def run_transfer_counter(self):
        """Count real client-side transfers (valid && ready) forever."""
        while True:
            await RisingEdge(self.axi_aclk)
            if self.rst_n.value != 1:
                continue
            try:
                vvec = int(self.dut.monbus_valid_in.value)
                rvec = int(self.dut.monbus_ready_in.value)
            except ValueError:
                continue
            for i in range(self.CLIENTS):
                if (vvec >> i) & 1 and (rvec >> i) & 1:
                    self.xfers[i] += 1

    async def run_stability_monitor(self):
        """AXI-style payload stability check on the arbitrated output port.

        While `monbus_valid` is asserted and `monbus_ready` is low, the
        payload presented at `monbus_packet` must not change.
        """
        prev_valid = 0
        prev_ready = 0
        prev_pkt = None
        while True:
            await RisingEdge(self.axi_aclk)
            if self.rst_n.value != 1:
                continue
            try:
                valid = int(self.dut.monbus_valid.value)
                ready = int(self.dut.monbus_ready.value)
                pkt = int(self.dut.monbus_packet.value)
            except ValueError:
                prev_valid, prev_ready, prev_pkt = 0, 0, None
                continue

            if (prev_valid == 1 and prev_ready == 0 and valid == 1
                    and prev_pkt is not None and pkt != prev_pkt):
                self.stability_violations += 1
                self.log.error(
                    f"payload changed while valid && !ready: "
                    f"0x{prev_pkt:x} -> 0x{pkt:x}")

            prev_valid, prev_ready, prev_pkt = valid, ready, pkt

    # ---- test phases ------------------------------------------------------

    async def phase_backpressured_hold(self, clients, cycles=16):
        """Sink held not-ready. The grant must not move and no transfer may
        occur. Returns (rotations, transfers_seen)."""
        self.dut.monbus_ready.value = 0
        self.request(clients)

        # let the arbiter settle on a grant
        await self.wait_clocks(self.clk_name, 4)
        base_xfers = list(self.xfers)
        ref_grant = self._grant_vector()
        grant_valid = int(self.dut.grant_valid.value)
        self.log.info(f"settled grant=0b{ref_grant:0{self.CLIENTS}b} "
                      f"grant_valid={grant_valid}")
        assert grant_valid == 1, \
            "arbiter never issued a grant with live requests"

        rotations = 0
        for cyc in range(cycles):
            await RisingEdge(self.axi_aclk)
            await FallingEdge(self.axi_aclk)   # sample settled mid-cycle
            g = self._grant_vector()
            if g != ref_grant:
                rotations += 1
                self.log.error(
                    f"cyc{cyc}: grant rotated 0b{ref_grant:0{self.CLIENTS}b} "
                    f"-> 0b{g:0{self.CLIENTS}b} with ready low")
                ref_grant = g

        moved = [self.xfers[i] - base_xfers[i] for i in range(self.CLIENTS)]
        self.grant_rotations_without_xfer = rotations
        return rotations, moved

    async def phase_drain(self, cycles=24):
        """Release the sink and let the requesting clients drain."""
        self.dut.monbus_ready.value = 1
        await self.wait_clocks(self.clk_name, cycles)
        self.request([])
        self.dut.monbus_ready.value = 0
        await self.wait_clocks(self.clk_name, 4)
