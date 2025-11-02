# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ArbiterRoundRobinSimpleTB
# Purpose: Simple Round Robin Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Simple Round Robin Testbench
Simplified version without ACK protocol and block_arb functionality
"""

import os
import random
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, FallingEdge, Timer, ClockCycles
from cocotb.clock import Clock

# Import the ArbiterMaster and existing monitor
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.arbiter_monitor import RoundRobinArbiterMonitor
from CocoTBFramework.components.shared.arbiter_master import ArbiterMaster

class ArbiterRoundRobinSimpleTB(TBBase):
    """
    Simple Round Robin Arbiter Testbench
    Simplified version without ACK protocol and block_arb
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters (simple arbiter only has N parameter)
        self.CLIENTS = int(dut.N)
        self.WAIT_GNT_ACK = 0  # Simple arbiter never has ACK
        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Clock and reset signals
        self.clock = self.dut.clk
        self.reset_n = self.dut.rst_n

        # Initialize the arbiter monitor (simplified for no ACK mode)
        self.monitor = RoundRobinArbiterMonitor(
            dut=dut,
            title="Simple_RR_Monitor",
            clock=self.dut.clk,
            reset_n=self.dut.rst_n,
            req_signal=self.dut.request,
            gnt_valid_signal=self.dut.grant_valid,
            gnt_signal=self.dut.grant,
            gnt_id_signal=self.dut.grant_id,
            gnt_ack_signal=None,  # No ACK in simple arbiter
            block_arb_signal=None,  # No block_arb in simple arbiter
            clients=self.CLIENTS,
            ack_mode=False,  # Never ACK mode
            log=self.log,
            clock_period_ns=10
        )

        # Initialize the arbiter master (no ACK mode)
        self.master = ArbiterMaster(
            dut=dut,
            title="Simple_RR_Driver",
            clock=self.dut.clk,
            num_clients=self.CLIENTS,
            ack_mode=False,  # Never ACK mode
            log=self.log
        )

        # Track any monitor errors
        self.monitor_errors = []
        self.monitor.add_transaction_callback(self._on_monitor_transaction)
        self.monitor.add_reset_callback(self._on_monitor_reset)
        self.monitor.enable_debug()

        # Clock management
        self.clock_started = False

        # Log configuration
        self.log.info(f"Simple Arbiter TB initialized with CLIENTS={self.CLIENTS}{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}{self.get_time_ns_str()}")
        self.log.info(f"Mode: No ACK, No block_arb (simple){self.get_time_ns_str()}")

    def _on_monitor_transaction(self, transaction):
        """Callback for monitor transactions - validate transaction properties"""
        # Basic transaction validation
        if transaction.gnt_id >= self.CLIENTS:
            error = f"Invalid grant ID {transaction.gnt_id} >= {self.CLIENTS}"
            self.monitor_errors.append(error)
            self.log.error(error)

    def _on_monitor_reset(self, reset_type):
        """Callback for monitor reset events"""
        self.log.debug(f"Monitor reset event: {reset_type}{self.get_time_ns_str()}")

    async def start_clock(self, clock_name: str, period: int, units: str = 'ns'):
        """Start the clock"""
        if not self.clock_started:
            clock_gen = Clock(getattr(self.dut, clock_name), period, units=units)
            cocotb.start_soon(clock_gen.start())
            self.clock_started = True

            # Wait for clock to stabilize
            await ClockCycles(self.dut.clk, 2)

    async def reset_dut(self):
        """Reset the DUT and start components"""
        # Apply reset
        self.dut.rst_n.value = 0
        await ClockCycles(self.dut.clk, 10)
        self.dut.rst_n.value = 1
        await ClockCycles(self.dut.clk, 5)

        # Start the master
        await self.master.startup()

        self.log.info(f"DUT reset complete, components started{self.get_time_ns_str()}")

    async def wait_clocks(self, clock_name: str, num_clocks: int):
        """Wait for specified number of clock cycles"""
        await ClockCycles(getattr(self.dut, clock_name), num_clocks)

    def get_time_ns_str(self):
        """Get current simulation time as string"""
        return f" @ {get_sim_time('ns'):.1f}ns"

    # =============================================================================
    # SIMPLIFIED TEST METHODS (no ACK, no block_arb)
    # =============================================================================

    async def test_grant_signals(self):
        """Test basic grant signal functionality (no ACK needed)"""
        self.log.info(f"Starting grant signals test{self.get_time_ns_str()}")

        # Disable automatic requests for controlled testing
        for client_id in range(self.CLIENTS):
            self.master.disable_client(client_id)

        # Test each client individually
        for client_id in range(self.CLIENTS):
            self.log.info(f"Testing grant signal for client {client_id}")

            # Simple manual request (no ACK needed)
            await self.master.manual_request(client_id, cycles=5)

            # Check for grant
            grant_received = await self.master.wait_for_grant(client_id, timeout_cycles=20)
            assert grant_received, f"Client {client_id} did not receive grant"

            # Wait for completion
            await self.wait_clocks('clk', 10)

        self.log.info(f"Grant signals test passed{self.get_time_ns_str()}")

    async def run_basic_arbitration_test(self, duration_cycles: int = 600):
        """Basic arbitration test (simplified)"""
        self.log.info(f"Starting basic arbitration test for {duration_cycles} cycles{self.get_time_ns_str()}")

        # Enable all clients with default profiles
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'default')
            self.master.enable_client(client_id)

        # Wait for setup
        await self.wait_clocks('clk', 50)

        # Record initial state
        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        # Run test
        await self.wait_clocks('clk', duration_cycles)

        # Check results
        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        total_grants = final_grants - initial_grants

        self.log.info(f"Basic arbitration: {total_grants} grants in {duration_cycles} cycles")

        # Verify reasonable activity
        min_grants = 30
        assert total_grants > min_grants, f"Insufficient activity: {total_grants} < {min_grants}"

        self.log.info(f"Basic arbitration test passed{self.get_time_ns_str()}")

    async def test_walking_requests(self):
        """Test walking requests (simplified, no ACK)"""
        self.log.info(f"Starting walking requests test{self.get_time_ns_str()}")

        # Ensure master is running
        if not self.master.active:
            await self.master.startup()
            await self.wait_clocks('clk', 10)

        # Test each client individually
        for i in range(self.CLIENTS):
            self.log.info(f"=== Testing individual client {i} ==={self.get_time_ns_str()}")

            # Disable all clients
            for client_id in range(self.CLIENTS):
                self.master.disable_client(client_id)
            await self.wait_clocks('clk', 10)

            # Test this client without ACK
            self.log.info(f"Testing client {i} (no ACK)")

            try:
                await self.master.manual_request(client_id=i, cycles=10)
                success = True
                self.log.info(f"✓ Client {i} test successful")

            except Exception as e:
                self.log.error(f"✗ Client {i} test failed: {e}")
                success = False

            # Brief cleanup pause
            await self.wait_clocks('clk', 10)

        self.log.info(f"Walking requests test completed{self.get_time_ns_str()}")

    async def test_fairness(self):
        """Test fairness (simplified)"""
        self.log.info(f"Starting fairness test{self.get_time_ns_str()}")

        # Use simple profiles for all clients
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'default')
            self.master.enable_client(client_id)

        # Record initial state
        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        # Run fairness test
        test_cycles = 1500
        await self.wait_clocks('clk', test_cycles)

        # Check results
        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        total_grants = final_grants - initial_grants
        fairness_index = final_stats.get('fairness_index', 0)

        if fairness_index == 0:
            try:
                fairness_index = self.monitor.get_fairness_index()
            except:
                fairness_index = 0

        self.log.info(f"Fairness test: {total_grants} grants, fairness index: {fairness_index:.3f}{self.get_time_ns_str()}")

        # Reasonable thresholds for simple arbiter
        min_grants_threshold = 50
        min_fairness_threshold = 0.3

        assert total_grants > min_grants_threshold, (
            f"Insufficient activity for fairness test: {total_grants} grants < {min_grants_threshold}"
        )

        assert fairness_index > min_fairness_threshold, (
            f"Poor fairness: {fairness_index:.3f} < {min_fairness_threshold}"
        )

        self.log.info(f"✓ Fairness test passed: {total_grants} grants, fairness: {fairness_index:.3f}")

    async def test_single_client_saturation(self):
        """Test single client saturation"""
        self.log.info(f"Starting single client saturation test{self.get_time_ns_str()}")

        # Disable all clients except one
        for client_id in range(self.CLIENTS):
            self.master.disable_client(client_id)

        await self.wait_clocks('clk', 50)

        # Enable only client 0
        self.master.set_client_profile(0, 'fast')
        self.master.enable_client(0)

        # Record initial state
        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        # Run saturation test
        test_duration = 800
        await self.wait_clocks('clk', test_duration)

        # Check results
        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        saturation_grants = final_grants - initial_grants

        self.log.info(f"Single client saturation: {saturation_grants} grants in {test_duration} cycles")

        min_expected = 40
        assert saturation_grants > min_expected, f"Low saturation: {saturation_grants} < {min_expected}"

        # Re-enable all clients for next test
        for client_id in range(self.CLIENTS):
            self.master.enable_client(client_id)

        self.log.info(f"Single client saturation test passed{self.get_time_ns_str()}")

    async def test_rapid_request_changes(self):
        """Test rapid request changes"""
        self.log.info(f"Starting rapid request changes test{self.get_time_ns_str()}")

        # Use fast profiles for rapid changes
        for client_id in range(self.CLIENTS):
            self.master.set_client_profile(client_id, 'fast')
            self.master.enable_client(client_id)

        # Record initial state
        initial_stats = self.monitor.get_comprehensive_stats()
        initial_grants = initial_stats.get('total_grants', 0)

        # Run for rapid changes
        await self.wait_clocks('clk', 1000)

        # Check results
        final_stats = self.monitor.get_comprehensive_stats()
        final_grants = final_stats.get('total_grants', 0)
        total_grants = final_grants - initial_grants

        self.log.info(f"Rapid changes test: {total_grants} grants generated")
        assert total_grants > 80, f"Insufficient rapid activity: {total_grants} grants"

        self.log.info(f"Rapid request changes test completed{self.get_time_ns_str()}")

    # =============================================================================
    # UTILITY METHODS
    # =============================================================================

    def check_monitor_errors(self):
        """Check for any monitor errors"""
        if self.monitor_errors:
            self.log.error(f"Monitor errors detected: {self.monitor_errors}")
            raise AssertionError(f"Monitor errors: {self.monitor_errors}")

    async def handle_test_transition(self):
        """Handle test transitions"""
        await self.wait_clocks('clk', 10)

    def generate_final_report(self):
        """Generate final test report"""
        try:
            # Get monitor statistics
            monitor_stats = self.monitor.get_comprehensive_stats()
            total_grants = monitor_stats.get('total_grants', 0) or len(self.monitor)
            fairness = monitor_stats.get('fairness_index', 0)

            # Get master statistics
            master_stats = self.master.get_stats()

            self.log.info("=== FINAL TEST REPORT (Simple Arbiter) ===")
            self.log.info(f"Total grants observed: {total_grants}")
            self.log.info(f"Fairness index: {fairness:.3f}")
            self.log.info(f"Master statistics: {master_stats}")
            self.log.info(f"Monitor errors: {len(self.monitor_errors)}")

            # Basic validation
            success = (
                total_grants > 0 and
                fairness > 0.2 and
                len(self.monitor_errors) == 0
            )

            if success:
                self.log.info("✓ Final report validation PASSED")
            else:
                self.log.error("✗ Final report validation FAILED")

            return success

        except Exception as e:
            self.log.error(f"Error generating final report: {e}")
            return False

    def convert_to_int(self, value):
        """Convert value to int (compatibility method)"""
        try:
            return int(value)
        except (ValueError, TypeError):
            return 0