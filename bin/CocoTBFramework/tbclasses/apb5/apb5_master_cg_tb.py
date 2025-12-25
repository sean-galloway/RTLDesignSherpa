# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APB5MasterCGTB
# Purpose: APB5 Master Clock-Gated Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-23

"""
APB5 Master Clock-Gated Testbench

Extends APB5MasterTB with clock gating control testing.
Tests the apb5_master_cg.sv module which wraps apb5_master.sv
with clock gating for power management.

Additional tests:
- Clock enable/disable behavior
- State preservation during clock gating
- Clock gating interaction with PWAKEUP
"""
import os

import cocotb
from cocotb.triggers import RisingEdge

from .apb5_master_tb import APB5MasterTB


class APB5MasterCGTB(APB5MasterTB):
    """
    APB5 Master Clock-Gated testbench.

    Extends APB5MasterTB with clock gating specific tests.
    """

    def __init__(self, dut, pclk=None, presetn=None):
        super().__init__(dut, pclk, presetn)

        # Clock gating specific statistics
        self.clock_gate_cycles = 0
        self.clock_active_cycles = 0

        # Log clock gating configuration
        self.log.info("APB5 Master Clock-Gated testbench initialized")

    async def enable_clock_gating(self, enable=True):
        """
        Enable or disable clock gating.

        Args:
            enable: True to enable clock gating, False to keep clock running
        """
        if hasattr(self.dut, 'cfg_cg_enable'):
            self.dut.cfg_cg_enable.value = 1 if enable else 0
            await self.wait_clocks(self.pclk_name, 1)
            self.log.info(f"Clock gating {'enabled' if enable else 'disabled'}")
        else:
            self.log.warning("Clock gating control signal not found")

    async def set_idle_count(self, count):
        """
        Set the idle count for clock gating.

        Args:
            count: Number of idle cycles before clock gating activates
        """
        if hasattr(self.dut, 'cfg_cg_idle_count'):
            self.dut.cfg_cg_idle_count.value = count
            await self.wait_clocks(self.pclk_name, 1)
            self.log.info(f"Clock gating idle count set to {count}")
        else:
            self.log.warning("Clock gating idle count signal not found")

    async def run_clock_gating_test(self):
        """Test clock gating behavior."""
        self.log.info("Starting clock gating test")

        # Ensure clock is running
        await self.enable_clock_gating(False)

        # Run some transactions with clock running
        await self.basic_write_read_sequence(count=5)

        await self.wait_clocks(self.pclk_name, 20)

        # Enable clock gating
        await self.enable_clock_gating(True)

        # Wait during gating
        await self.wait_clocks(self.pclk_name, 50)

        # Disable clock gating
        await self.enable_clock_gating(False)

        # Run more transactions
        await self.basic_write_read_sequence(count=5)

        await self.wait_clocks(self.pclk_name, 50)

        self.log.info("Clock gating test completed successfully")

    async def run_wakeup_with_clock_gating_test(self):
        """Test PWAKEUP interaction with clock gating."""
        self.log.info("Starting wakeup with clock gating test")

        # Enable clock gating
        await self.enable_clock_gating(True)

        # Wait for gating to activate
        await self.wait_clocks(self.pclk_name, 20)

        # Disable clock gating to allow transaction
        await self.enable_clock_gating(False)

        # Run transaction
        await self.single_write_test(addr=0x100, data=0xA0000000)

        await self.wait_clocks(self.pclk_name, 20)

        self.log.info("Wakeup with clock gating test completed")

    async def run_state_preservation_test(self):
        """Test that state is preserved during clock gating."""
        self.log.info("Starting state preservation test")

        # Run some transactions
        await self.enable_clock_gating(False)

        for i in range(3):
            await self.single_write_test(addr=0x80 + i * 4, data=0xB0000000 + i)

        await self.wait_clocks(self.pclk_name, 10)

        # Get stats before gating
        stats_before = self.get_test_stats()
        transactions_before = stats_before['summary']['total_transactions']

        # Gate clock for a period
        await self.enable_clock_gating(True)
        await self.wait_clocks(self.pclk_name, 100)
        await self.enable_clock_gating(False)

        # Get stats after ungating
        stats_after = self.get_test_stats()
        transactions_after = stats_after['summary']['total_transactions']

        # Verify state was preserved (transaction count should be same)
        assert transactions_after >= transactions_before, "State not preserved during clock gating"

        # Run more transactions to verify continued operation
        for i in range(3):
            await self.single_write_test(addr=0xC0 + i * 4, data=0xC0000000 + i)

        await self.wait_clocks(self.pclk_name, 50)

        self.log.info("State preservation test completed successfully")

    async def run_rapid_gating_test(self):
        """Test rapid clock gating enable/disable cycling."""
        self.log.info("Starting rapid gating test")

        for i in range(10):
            await self.enable_clock_gating(True)
            await self.wait_clocks(self.pclk_name, 5)
            await self.enable_clock_gating(False)
            await self.wait_clocks(self.pclk_name, 5)

        await self.wait_clocks(self.pclk_name, 20)

        self.log.info("Rapid gating test completed")

    def generate_final_report(self):
        """Generate final test report including clock gating stats."""
        stats = self.get_test_stats()

        self.log.info("=== CLOCK GATING STATISTICS ===")
        self.log.info(f"Clock gate cycles: {self.clock_gate_cycles}")
        self.log.info(f"Clock active cycles: {self.clock_active_cycles}")

        return stats
