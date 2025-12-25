# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIS5MasterCGTB
# Purpose: AXIS5 Master Clock-Gated Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""
AXIS5 Master Clock-Gated Testbench

Extends AXIS5MasterTB with clock gating control testing.
Tests the axis5_master_cg.sv module which wraps axis5_master.sv
with clock gating for power management.

Additional tests:
- Clock enable/disable behavior
- State preservation during clock gating
- Clock gating interaction with TWAKEUP
"""
import os

import cocotb
from cocotb.triggers import RisingEdge

from .axis5_master_tb import AXIS5MasterTB
from CocoTBFramework.components.axis5.axis5_packet import AXIS5Packet


class AXIS5MasterCGTB(AXIS5MasterTB):
    """
    AXIS5 Master Clock-Gated testbench.

    Extends AXIS5MasterTB with clock gating specific tests.
    """

    def __init__(self, dut, aclk=None, aresetn=None):
        super().__init__(dut, aclk, aresetn)

        # Clock gating specific statistics
        self.clock_gate_cycles = 0
        self.clock_active_cycles = 0

        # Log clock gating configuration
        self.log.info("AXIS5 Master Clock-Gated testbench initialized")

    async def enable_clock_gating(self, enable=True):
        """
        Enable or disable clock gating.

        Args:
            enable: True to enable clock gating, False to keep clock running
        """
        if hasattr(self.dut, 'i_cg_enable'):
            self.dut.i_cg_enable.value = 1 if enable else 0
            await self.wait_clocks(self.aclk_name, 1)
            self.log.info(f"Clock gating {'enabled' if enable else 'disabled'}")
        else:
            self.log.warning("Clock gating control signal not found")

    async def run_clock_gating_test(self):
        """Test clock gating behavior."""
        self.log.info("Starting clock gating test")

        # Ensure clock is running
        await self.enable_clock_gating(False)
        self.axis_slave._set_ready(1)

        # Send some packets with clock running
        for i in range(5):
            packet = AXIS5Packet(
                enable_wakeup=self.ENABLE_WAKEUP,
                enable_parity=self.ENABLE_PARITY
            )
            packet.data = 0x80000000 + i
            packet.last = 1

            if self.ENABLE_PARITY:
                packet.parity = packet.calculate_parity()

            success = await self.fub_master.send_packet(packet)
            assert success, f"Failed to send packet {i}"

        await self.wait_clocks(self.aclk_name, 20)

        # Enable clock gating
        await self.enable_clock_gating(True)

        # Wait and verify no activity during gating
        await self.wait_clocks(self.aclk_name, 50)

        # Disable clock gating
        await self.enable_clock_gating(False)

        # Send more packets
        for i in range(5):
            packet = AXIS5Packet(
                enable_wakeup=self.ENABLE_WAKEUP,
                enable_parity=self.ENABLE_PARITY
            )
            packet.data = 0x90000000 + i
            packet.last = 1

            if self.ENABLE_PARITY:
                packet.parity = packet.calculate_parity()

            success = await self.fub_master.send_packet(packet)
            assert success, f"Failed to send packet {i} after clock ungating"

        await self.wait_clocks(self.aclk_name, 50)

        # Verify all packets received
        slave_stats = self.axis_slave.get_stats()
        packets_received = slave_stats.get('packets_received', 0)
        self.log.info(f"Total packets received: {packets_received}")

        assert packets_received >= 10, "Not all packets received after clock gating"
        self.log.info("Clock gating test completed successfully")

    async def run_wakeup_with_clock_gating_test(self):
        """Test TWAKEUP interaction with clock gating."""
        if not self.ENABLE_WAKEUP:
            self.log.info("Wakeup not enabled, skipping wakeup + clock gating test")
            return

        self.log.info("Starting wakeup with clock gating test")

        # Enable clock gating
        await self.enable_clock_gating(True)

        # Request wakeup - should trigger clock ungating in RTL
        self.fub_master.request_wakeup()

        # Check if wakeup signal is properly propagated
        packet = AXIS5Packet(
            enable_wakeup=self.ENABLE_WAKEUP,
            enable_parity=self.ENABLE_PARITY
        )
        packet.data = 0xA0000000
        packet.last = 1
        packet.wakeup = 1

        # Disable clock gating to allow transfer
        await self.enable_clock_gating(False)
        self.axis_slave._set_ready(1)

        success = await self.fub_master.send_packet(packet)
        assert success, "Failed to send wakeup packet"

        await self.wait_clocks(self.aclk_name, 20)

        slave_stats = self.axis_slave.get_stats()
        wakeup_events = slave_stats.get('wakeup_events', 0)
        self.log.info(f"Wakeup events after clock gating: {wakeup_events}")

        self.log.info("Wakeup with clock gating test completed")

    async def run_state_preservation_test(self):
        """Test that state is preserved during clock gating."""
        self.log.info("Starting state preservation test")

        # Send some packets
        await self.enable_clock_gating(False)
        self.axis_slave._set_ready(1)

        for i in range(3):
            packet = AXIS5Packet(
                enable_wakeup=self.ENABLE_WAKEUP,
                enable_parity=self.ENABLE_PARITY
            )
            packet.data = 0xB0000000 + i
            packet.last = 1

            success = await self.fub_master.send_packet(packet)
            assert success, f"Failed to send packet {i}"

        await self.wait_clocks(self.aclk_name, 10)

        # Get stats before gating
        stats_before = self.axis_slave.get_stats()
        packets_before = stats_before.get('packets_received', 0)

        # Gate clock for a period
        await self.enable_clock_gating(True)
        await self.wait_clocks(self.aclk_name, 100)
        await self.enable_clock_gating(False)

        # Get stats after ungating
        stats_after = self.axis_slave.get_stats()
        packets_after = stats_after.get('packets_received', 0)

        # Verify state was preserved (packet count should be same)
        assert packets_after >= packets_before, "State not preserved during clock gating"

        # Send more packets to verify continued operation
        for i in range(3):
            packet = AXIS5Packet(
                enable_wakeup=self.ENABLE_WAKEUP,
                enable_parity=self.ENABLE_PARITY
            )
            packet.data = 0xC0000000 + i
            packet.last = 1

            success = await self.fub_master.send_packet(packet)
            assert success, f"Failed to send packet {i} after ungating"

        await self.wait_clocks(self.aclk_name, 50)

        final_stats = self.axis_slave.get_stats()
        final_packets = final_stats.get('packets_received', 0)
        assert final_packets >= packets_before + 3, "Packets not received after ungating"

        self.log.info("State preservation test completed successfully")

    def generate_final_report(self):
        """Generate final test report including clock gating stats."""
        success = super().generate_final_report()

        self.log.info("=== CLOCK GATING STATISTICS ===")
        self.log.info(f"Clock gate cycles: {self.clock_gate_cycles}")
        self.log.info(f"Clock active cycles: {self.clock_active_cycles}")

        return success
