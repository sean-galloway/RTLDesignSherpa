# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ArbiterMonbusCommonTB
# Purpose: Updated Arbiter MonBus Common Testbench - Modular Test Architecture
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Updated Arbiter MonBus Common Testbench - Modular Test Architecture

This is the main testbench that imports and orchestrates all test modules.
The tests are now organized in separate files for better maintainability.

Test Organization:
- basic_tests.py: Monitor enable/disable, packet generation, basic filtering
- threshold_tests.py: Latency, starvation, fairness, active thresholds
- error_tests.py: Starvation, timeout, protocol, fairness violation detection
- performance_tests.py: Grant/ACK tracking, performance events
- corner_case_tests.py: FIFO edge cases, reset behavior, config edge cases
- stress_tests.py: Stress and reliability tests

Updated to use synchronized types from monbus_types.py and centralized MonitorConfig.
"""

import os
import random
import cocotb
from cocotb.triggers import RisingEdge, Timer, ClockCycles
from cocotb.utils import get_sim_time
from enum import Enum
from dataclasses import dataclass
from typing import Dict, List, Optional, Any

# Use your existing TBBase framework
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.tbclasses.monbus.monbus_slave import MonbusSlave
from CocoTBFramework.tbclasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS

# ✅ UPDATED IMPORTS - Use synchronized types and clean import structure
from CocoTBFramework.tbclasses.monbus.monbus_types import ProtocolType, PktType
from CocoTBFramework.tbclasses.amba.arbiter_monbus.monitor_config import MonitorConfig, TestResult, ConfigUtils

# Import all test modules (they now use centralized imports internally)
from .test_framework import TestConfiguration, TestFramework
from .basic_tests import BasicFunctionalityTest
from .threshold_tests import ThresholdMonitoringTest
from .error_tests import ErrorDetectionTest
from .performance_tests import PerformanceMonitoringTest
from .corner_case_tests import FifoCornerCaseTest, ResetBehaviorTest, ConfigurationEdgeCaseTest
from .stress_tests import StressAndReliabilityTest


class ArbiterMonbusCommonTB(TBBase):
    """Enhanced testbench using TBBase framework with modular test architecture"""

    def __init__(self, dut, test_level='basic'):
        super().__init__(dut)

        self.test_level = test_level

        # Simple configuration detection
        self.config = TestConfiguration(dut)
        self.log.info(f"Detected configuration: {self.config}")

        # Test registry and execution engine
        self.test_results = {}

        self.clients = int(dut.CLIENTS.value)
        self.fifo_depth = int(dut.MON_FIFO_DEPTH.value)
        self.agent_id = int(dut.MON_AGENT_ID.value)
        self.unit_id = int(dut.MON_UNIT_ID.value)
        self.wait_gnt_ack = int(dut.WAIT_GNT_ACK.value)
        self.n = max(1, (self.clients - 1).bit_length())  # Calculate N = $clog2(CLIENTS)

        # Initialize using existing MonbusSlave
        self.monbus_slave = None
        self.current_config = None
        self.test_results = {}

        # Arbiter simulation state
        self.current_requests = 0
        self.last_grant_id = 0
        self.grant_active = False
        self.ack_timeout_counter = 0
        self.arbiter_enabled = True

        # Test class instances - will be instantiated in setup
        self.basic_test = None
        self.threshold_test = None
        self.error_test = None
        self.performance_test = None
        self.fifo_corner_test = None
        self.reset_behavior_test = None
        self.config_edge_test = None
        self.stress_test = None
        self.test_framework = None

    async def setup_testbench(self):
        """Your existing setup method - keep everything exactly as-is"""
        self.log.info("🚀 Setting up enhanced testbench...")

        try:
            # ALL YOUR EXISTING MonBus slave initialization - keep as-is
            self.monbus_slave = MonbusSlave(
                dut=self.dut,
                title="MonBusMonitor",
                prefix="",
                clock=self.dut.clk,
                bus_name="monbus",
                pkt_prefix="",
                expected_protocol=ProtocolType.PROTOCOL_ARB,
                expected_unit_id=self.unit_id,
                expected_agent_id=self.agent_id,
                timeout_cycles=1000,
                log=self.log,
                super_debug=False,
                randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fast']['slave'])
            )

            # ALL YOUR EXISTING arbiter initialization - keep as-is
            await self.initialize_arbiter_outputs()
            cocotb.start_soon(self.arbiter_simulation_task())

            # ALL YOUR EXISTING test class initialization - keep as-is
            self.basic_test = BasicFunctionalityTest(self)
            self.threshold_test = ThresholdMonitoringTest(self)
            self.error_test = ErrorDetectionTest(self)
            self.performance_test = PerformanceMonitoringTest(self)
            self.fifo_corner_test = FifoCornerCaseTest(self)
            self.reset_behavior_test = ResetBehaviorTest(self)
            self.config_edge_test = ConfigurationEdgeCaseTest(self)
            self.stress_test = StressAndReliabilityTest(self)

            # ADD ONLY THESE 2 LINES at the end:
            # Initialize new test framework after all test classes exist
            self.test_framework = TestFramework(self)
            
            self.log.info("✅ Testbench setup completed successfully")

        except Exception as e:
            self.log.error(f"❌ Testbench setup failed: {e}")
            raise

    async def reset_dut(self, reset_duration_clks: int = 10):
        """
        Perform complete DUT reset sequence

        Args:
            reset_duration_clks: Number of clock cycles to hold reset asserted (default: 10)

        This method:
        1. Sets reset to 0 (asserted) and clears all inputs
        2. Waits specified number of clocks
        3. Releases reset to 1 (deasserted)
        4. Waits 10 clocks for reset to propagate
        """
        self.log.info(f"🔄 Starting DUT reset sequence ({reset_duration_clks} cycles)...")

        # STEP 1: Assert reset (active low) and clear all inputs
        self.log.debug("Step 1: Asserting reset and clearing all inputs")
        self.dut.rst_n.value = 0  # Assert reset (active low)

        # Clear all inputs to safe values
        if hasattr(self.dut, 'cfg_max_thresh'):
            self.dut.cfg_max_thresh.value = 0
        if hasattr(self.dut, 'request'):
            self.dut.request.value = 0
        if hasattr(self.dut, 'grant_valid'):
            self.dut.grant_valid.value = 0
        if hasattr(self.dut, 'grant'):
            self.dut.grant.value = 0
        if hasattr(self.dut, 'grant_id'):
            self.dut.grant_id.value = 0
        if hasattr(self.dut, 'grant_ack'):
            self.dut.grant_ack.value = 0
        if hasattr(self.dut, 'block_arb'):
            self.dut.block_arb.value = 0

        # Clear all monitor configuration inputs
        if hasattr(self.dut, 'cfg_mon_enable'):
            self.dut.cfg_mon_enable.value = 0
        if hasattr(self.dut, 'cfg_mon_pkt_type_enable'):
            self.dut.cfg_mon_pkt_type_enable.value = 0
        if hasattr(self.dut, 'cfg_mon_latency_thresh'):
            self.dut.cfg_mon_latency_thresh.value = 0
        if hasattr(self.dut, 'cfg_mon_starvation_thresh'):
            self.dut.cfg_mon_starvation_thresh.value = 0
        if hasattr(self.dut, 'cfg_mon_fairness_thresh'):
            self.dut.cfg_mon_fairness_thresh.value = 0
        if hasattr(self.dut, 'cfg_mon_active_thresh'):
            self.dut.cfg_mon_active_thresh.value = 0
        if hasattr(self.dut, 'cfg_mon_ack_timeout_thresh'):
            self.dut.cfg_mon_ack_timeout_thresh.value = 0
        if hasattr(self.dut, 'cfg_mon_efficiency_thresh'):
            self.dut.cfg_mon_efficiency_thresh.value = 0
        if hasattr(self.dut, 'cfg_mon_sample_period'):
            self.dut.cfg_mon_sample_period.value = 0

        # Clear monbus ready input
        if hasattr(self.dut, 'monbus_ready'):
            self.dut.monbus_ready.value = 1  # Ready to accept data

        # Clear any optional weighted arbiter inputs
        if hasattr(self.dut, 'client_weights'):
            self.dut.client_weights.value = 0
        if hasattr(self.dut, 'client_credits'):
            self.dut.client_credits.value = 0
        if hasattr(self.dut, 'arb_state'):
            self.dut.arb_state.value = 0
        if hasattr(self.dut, 'weight_update_active'):
            self.dut.weight_update_active.value = 0

        # STEP 2: Wait specified duration with reset asserted
        self.log.debug(f"Step 2: Waiting {reset_duration_clks} clocks with reset asserted")
        await self.wait_clocks('clk', reset_duration_clks)

        # STEP 3: Release reset (deassert)
        self.log.debug("Step 3: Deasserting reset")
        self.dut.rst_n.value = 1  # Deassert reset (active low)

        # STEP 4: Wait 10 clocks for reset to propagate and settle
        self.log.debug("Step 4: Waiting 10 clocks for reset to propagate")
        await self.wait_clocks('clk', 10)

        # STEP 5: Reset internal testbench state
        self.log.debug("Step 5: Resetting internal testbench state")
        self.current_requests = 0
        self.grant_active = False
        self.ack_timeout_counter = 0
        self.last_grant_id = 0
        if hasattr(self, 'monbus_slave') and self.monbus_slave:
            self.monbus_slave.reset_statistics()

        self.log.info(f"✅ DUT reset sequence completed successfully ({reset_duration_clks} cycles)")

    # Optional: Keep apply_reset as an alias for backward compatibility
    async def apply_reset(self, reset_duration_clks: int = 10):
        """Alias for reset_dut for backward compatibility with existing tests"""
        await self.reset_dut(reset_duration_clks)

    async def wait_for_fifo_empty(self, max_cycles: int = 200):
        """
        Wait for the FIFO to be completely empty (monbus_valid = 0)

        This method:
        1. Ensures monbus_ready is asserted to drain the FIFO
        2. Waits in a loop until monbus_valid = 0
        3. Times out if FIFO doesn't drain within max_cycles

        Args:
            max_cycles: Maximum cycles to wait for FIFO to empty
        """
        start_time = self.get_time_ns_str()
        self.log.debug(f"⏳ Waiting for FIFO to empty (max {max_cycles} cycles)...{start_time}")

        # Ensure monbus_ready is asserted to enable draining
        if hasattr(self.dut, 'monbus_ready'):
            self.dut.monbus_ready.value = 1

        cycles_waited = 0
        initial_fifo_count = int(self.dut.debug_fifo_count.value) if hasattr(self.dut, 'debug_fifo_count') else -1
        initial_valid = int(self.dut.monbus_valid.value) if hasattr(self.dut, 'monbus_valid') else 0

        self.log.debug(f"Starting drain: valid={initial_valid}, count={initial_fifo_count} @ {self.get_time_ns_str()}")

        # Wait until monbus_valid goes to 0
        while cycles_waited < max_cycles:
            monbus_valid = int(self.dut.monbus_valid.value) if hasattr(self.dut, 'monbus_valid') else 0
            fifo_count = int(self.dut.debug_fifo_count.value) if hasattr(self.dut, 'debug_fifo_count') else 0

            # FIFO is empty when monbus_valid = 0 AND fifo_count = 0
            if monbus_valid == 0 and fifo_count == 0:
                end_time = self.get_time_ns_str()
                self.log.debug(f"✅ FIFO empty after {cycles_waited} cycles @ {end_time}")
                return True

            # Log state changes for debugging
            if cycles_waited == 0 or cycles_waited % 25 == 0:
                current_time = self.get_time_ns_str()
                self.log.debug(f"Drain progress: cycle {cycles_waited}, valid={monbus_valid}, count={fifo_count} @ {current_time}")

            await self.wait_clocks('clk', 1)
            cycles_waited += 1

        # Timeout reached
        final_valid = int(self.dut.monbus_valid.value) if hasattr(self.dut, 'monbus_valid') else 0
        final_count = int(self.dut.debug_fifo_count.value) if hasattr(self.dut, 'debug_fifo_count') else 0
        final_time = self.get_time_ns_str()

        self.log.warning(f"⚠️  FIFO drain timeout after {max_cycles} cycles @ {final_time}")
        self.log.warning(f"   Initial: valid={initial_valid}, count={initial_fifo_count}")
        self.log.warning(f"   Final: valid={final_valid}, count={final_count}")
        return False

    async def disable_monitor_and_clear_packets(self):
        """
        Simple version: disable monitor and clear testbench packet buffer
        """
        self.log.info(f"🔄 Disabling monitor and clearing packet buffer...{self.get_time_ns_str()}")

        # Disable monitor
        if hasattr(self.dut, 'cfg_mon_enable'):
            self.dut.cfg_mon_enable.value = 0

        # Wait for disable to take effect
        await self.wait_falling_clocks('clk')
        while self.dut.monbus_valid.value == 1:
            await self.wait_falling_clocks('clk')

        self.log.info(f"🔄 monbus_valid no longer asserted...{self.get_time_ns_str()}")


        packets_before = len(self.monbus_slave.received_packets)
        self.monbus_slave.clear_received_packets()
        self.monbus_slave.reset_statistics()
        self.log.debug(f"Cleared {packets_before} packets from testbench buffer{self.get_time_ns_str()}")

        self.log.info("✅ Monitor disabled and packets cleared")
        return True

    async def disable_monitor_and_drain_fifo(self, max_drain_cycles: int = 200):
        """
        Disable monitor and clear ALL packets (hardware + testbench)
        """
        self.log.info(f"🔄 Disabling monitor and clearing all packets...{self.get_time_ns_str()}")

        # STEP 1: Disable monitor
        self.log.debug(f"Step 1: Disabling monitor{self.get_time_ns_str()}")
        if hasattr(self.dut, 'cfg_mon_enable'):
            self.dut.cfg_mon_enable.value = 0

        # Wait for disable to take effect
        await self.wait_falling_clocks('clk')
        while self.dut.monbus_valid.value == 1:
            await self.wait_falling_clocks('clk')

        self.log.info(f"🔄 monbus_valid no longer asserted...{self.get_time_ns_str()}")

        # STEP 3: Clear the testbench packet buffer (this is the key fix!)
        self.log.debug(f"Step 3: Clearing testbench packet buffer{self.get_time_ns_str()}")
        # Force clear all received packets from testbench
        self.monbus_slave.clear_received_packets()
        self.monbus_slave.reset_statistics()
        self.log.debug(f"Cleared testbench packets, buffer now has {len(self.monbus_slave.received_packets)} packets")

        # STEP 4: Ensure monbus_ready is asserted for any future draining
        if hasattr(self.dut, 'monbus_ready'):
            self.dut.monbus_ready.value = 1

        # STEP 5: Wait for any remaining hardware FIFO to drain (optional)
        await self.wait_for_fifo_empty(50)  # Shorter timeout since testbench is cleared

        self.log.info(f"✅ Monitor disabled and all packets cleared{self.get_time_ns_str()}")
        return True

    async def prepare_clean_test_state_with_fifo_drain(self):
        """
        Enhanced version of prepare_clean_test_state that includes FIFO draining

        Use this instead of prepare_clean_test_state() for enable/disable tests
        """
        self.log.info(f"🧹 Preparing clean test state with FIFO drain...{self.get_time_ns_str()}")

        # STEP 1: Disable monitor and drain FIFO completely
        await self.disable_monitor_and_drain_fifo()

        # STEP 2: Clear all arbiter activity
        await self.set_idle_arbiter_state()

        # STEP 3: Wait for system to stabilize
        await self.wait_clocks('clk', 10)

        # STEP 4: Final verification that FIFO is empty
        final_valid = int(self.dut.monbus_valid.value) if hasattr(self.dut, 'monbus_valid') else 0
        final_count = int(self.dut.debug_fifo_count.value) if hasattr(self.dut, 'debug_fifo_count') else 0

        if final_valid != 0 or final_count != 0:
            self.log.error(f"❌ Clean state verification failed: valid={final_valid}, count={final_count}{self.get_time_ns_str()}")
            return False

        self.log.info(f"✅ Clean test state with empty FIFO prepared successfully{self.get_time_ns_str()}")
        return True

    async def initialize_arbiter_outputs(self):
        """Initialize all arbiter output signals to safe idle state"""
        self.log.debug(f"Initializing arbiter outputs...{self.get_time_ns_str()}")

        # Initialize arbiter outputs to idle
        self.dut.grant_valid.value = 0
        self.dut.grant.value = 0
        self.dut.grant_id.value = 0

        # Initialize inputs we control
        self.dut.request.value = 0
        self.dut.grant_ack.value = 0
        self.dut.block_arb.value = 0

        # Initialize optional weighted arbiter inputs
        if hasattr(self.dut, 'client_weights'):
            self.dut.client_weights.value = 0
        if hasattr(self.dut, 'client_credits'):
            self.dut.client_credits.value = 0
        if hasattr(self.dut, 'arb_state'):
            self.dut.arb_state.value = 0
        if hasattr(self.dut, 'weight_update_active'):
            self.dut.weight_update_active.value = 0

        # Reset internal state
        self.current_requests = 0
        self.grant_active = False
        self.ack_timeout_counter = 0

        await self.wait_clocks('clk', 2)
        self.log.debug("Arbiter outputs initialized")

    async def apply_monitor_config(self, config=None):
        """Apply monitor configuration - supports both MonitorConfig objects and dicts"""

        # Handle different config types
        if config is None:
            # Use default configuration
            config = MonitorConfig()
        elif isinstance(config, dict):
            # Convert dict to MonitorConfig object
            # Create default config and override with dict values
            default_config = MonitorConfig()
            config_params = {}

            # Map dict keys to MonitorConfig parameters
            key_mapping = {
                'cfg_mon_enable': 'enable',
                'cfg_mon_pkt_type_enable': 'pkt_type_enable',
                'cfg_mon_latency_thresh': 'latency_thresh',
                'cfg_mon_starvation_thresh': 'starvation_thresh',
                'cfg_mon_fairness_thresh': 'fairness_thresh',
                'cfg_mon_active_thresh': 'active_thresh',
                'cfg_mon_ack_timeout_thresh': 'ack_timeout_thresh',
                'cfg_mon_efficiency_thresh': 'efficiency_thresh',
                'cfg_mon_sample_period': 'sample_period'
            }

            # Start with defaults
            config_params = {
                'enable': default_config.enable,
                'pkt_type_enable': default_config.pkt_type_enable,
                'latency_thresh': default_config.latency_thresh,
                'starvation_thresh': default_config.starvation_thresh,
                'fairness_thresh': default_config.fairness_thresh,
                'active_thresh': default_config.active_thresh,
                'ack_timeout_thresh': default_config.ack_timeout_thresh,
                'efficiency_thresh': default_config.efficiency_thresh,
                'sample_period': default_config.sample_period
            }

            # Override with dict values
            for dict_key, param_key in key_mapping.items():
                if dict_key in config:
                    config_params[param_key] = config[dict_key]

            # Create MonitorConfig object
            config = MonitorConfig(**config_params)

        self.log.info(f"📝 Applying monitor configuration: {config}{self.get_time_ns_str()}")

        try:
            # Apply configuration to DUT
            self.dut.cfg_mon_enable.value = int(config.enable)
            self.dut.cfg_mon_pkt_type_enable.value = config.pkt_type_enable
            self.dut.cfg_mon_latency_thresh.value = config.latency_thresh
            self.dut.cfg_mon_starvation_thresh.value = config.starvation_thresh
            self.dut.cfg_mon_fairness_thresh.value = config.fairness_thresh
            self.dut.cfg_mon_active_thresh.value = config.active_thresh
            self.dut.cfg_mon_ack_timeout_thresh.value = config.ack_timeout_thresh
            self.dut.cfg_mon_efficiency_thresh.value = config.efficiency_thresh
            self.dut.cfg_mon_sample_period.value = config.sample_period

            # Wait for configuration to propagate
            await self.wait_clocks('clk', 5)

            # Verify configuration was applied correctly
            verification_passed = True
            if hasattr(self.dut, 'cfg_mon_enable'):
                actual_enable = int(self.dut.cfg_mon_enable.value)
                if actual_enable != int(config.enable):
                    self.log.error(f"Enable mismatch: expected {config.enable}, got {actual_enable}")
                    verification_passed = False

            if hasattr(self.dut, 'cfg_mon_pkt_type_enable'):
                actual_config = int(self.dut.cfg_mon_pkt_type_enable.value)
                if actual_config != config.pkt_type_enable:
                    self.log.error(f"Expected pkt_type_enable: 0x{config.pkt_type_enable:04x}")
                    self.log.error(f"Actual pkt_type_enable:   0x{actual_config:04x}")
                    verification_passed = False
                else:
                    self.log.info(f"✅ Configuration verified: pkt_type_enable = 0x{actual_config:04x}")

            if not verification_passed:
                raise RuntimeError("Monitor configuration verification failed")

            self.current_config = config
            self.log.info("Monitor configuration applied and verified successfully")

        except Exception as e:
            self.log.error(f"Exception in apply_monitor_config: {e}")
            raise

    async def prepare_clean_test_state(self):
        """Prepare a clean state before each test"""
        self.log.info(f"🧹 Preparing clean test state...{self.get_time_ns_str()}")

        # STEP 1: Disable monitor
        await self.apply_monitor_config(MonitorConfig.disabled())

        # STEP 2: Clear all arbiter activity
        await self.set_idle_arbiter_state()

        # STEP 3: Drain any residual packets from hardware and testbench
        await self.drain_all_system_packets()

        # STEP 4: Reset statistics
        self.monbus_slave.reset_statistics()

        # STEP 5: Wait for system to stabilize
        await self.wait_clocks('clk', 10)

        self.log.info("✅ Clean test state prepared")

    async def set_idle_arbiter_state(self):
        """Set arbiter to completely idle state"""
        self.log.debug("Setting arbiter to idle state...")

        # Disable arbiter simulation temporarily
        self.arbiter_enabled = False

        # Clear all inputs
        self.dut.request.value = 0
        self.dut.grant_ack.value = 0
        self.dut.block_arb.value = 0

        # Clear all arbiter outputs
        self.dut.grant_valid.value = 0
        self.dut.grant.value = 0
        self.dut.grant_id.value = 0

        # Reset internal state
        self.current_requests = 0
        self.grant_active = False
        self.ack_timeout_counter = 0

        # Wait for idle state to propagate
        await self.wait_clocks('clk', 5)

        # Re-enable arbiter simulation
        self.arbiter_enabled = True

        self.log.debug("Arbiter set to idle state")

    # =================================================================
    # ARBITER SIMULATION LOGIC
    # =================================================================

    async def arbiter_simulation_task(self):
        """Background task that simulates arbiter behavior"""
        self.log.debug(f"Starting arbiter simulation task...{self.get_time_ns_str()}")

        while True:
            try:
                if self.arbiter_enabled:
                    await self.simulate_arbiter_cycle()
                await self.wait_clocks('clk', 1)
            except Exception as e:
                self.log.error(f"Error in arbiter simulation: {e}")
                break

    async def simulate_arbiter_cycle(self):
        """Simulate one cycle of arbiter behavior"""
        # Read current request state
        current_req = int(self.dut.request.value)
        block_arb = int(self.dut.block_arb.value) if hasattr(self.dut, 'block_arb') else 0

        # Handle ACK timeout if grant is pending
        if self.grant_active:
            if self.wait_gnt_ack:
                # Check for ACK
                current_ack = int(self.dut.grant_ack.value)
                if current_ack & (1 << self.last_grant_id):
                    # ACK received, clear grant
                    self.dut.grant_valid.value = 0
                    self.dut.grant.value = 0
                    self.grant_active = False
                    self.ack_timeout_counter = 0
                else:
                    # Increment timeout counter
                    self.ack_timeout_counter += 1
                    if self.ack_timeout_counter > 64:  # Timeout threshold
                        # Force clear grant on timeout
                        self.dut.grant_valid.value = 0
                        self.dut.grant.value = 0
                        self.grant_active = False
                        self.ack_timeout_counter = 0
            else:
                # No ACK required, clear grant after one cycle
                self.dut.grant_valid.value = 0
                self.dut.grant.value = 0
                self.grant_active = False

        # Grant new request if no grant active and not blocked
        if not self.grant_active and current_req and not block_arb:
            await self.issue_grant(current_req)

    async def issue_grant(self, request_mask: int):
        """Issue a grant to one of the requesting clients"""
        # Simple round-robin arbitration
        candidates = []
        for i in range(self.clients):
            if request_mask & (1 << i):
                candidates.append(i)

        if candidates:
            # Round-robin: pick next client after last grant
            try:
                start_idx = candidates.index(self.last_grant_id) + 1
            except ValueError:
                start_idx = 0

            if start_idx >= len(candidates):
                start_idx = 0

            grant_client = candidates[start_idx]

            # Issue grant
            self.dut.grant_valid.value = 1
            self.dut.grant.value = 1 << grant_client
            self.dut.grant_id.value = grant_client

            # Update state
            self.last_grant_id = grant_client
            self.grant_active = True
            self.ack_timeout_counter = 0

    async def drain_all_system_packets(self):
        """Comprehensive packet draining from both hardware and testbench"""
        self.log.debug(f"Draining all system packets...{self.get_time_ns_str()}")

        # Drain multiple times to handle any pipeline delays
        total_drained = 0

        for drain_round in range(3):
            packets = await self.monbus_slave.get_received_packets(
                timeout_cycles=20,
                drain_all=True,
                clear_after=True
            )
            total_drained += len(packets)

            if len(packets) == 0:
                break  # No more packets to drain

        self.log.debug(f"Drained {total_drained} residual packets{self.get_time_ns_str()}")

    async def finish_test_gracefully(self):
        """Clean up after each test"""
        self.log.debug(f"Finishing test gracefully...{self.get_time_ns_str()}")

        # Set idle state
        await self.set_idle_arbiter_state()

        # Wait for any pending operations
        await self.wait_clocks('clk', 5)

    # =================================================================
    # ACTIVITY GENERATION METHODS
    # =================================================================

    async def generate_arbiter_activity(self, cycles: int, pattern: str = "random"):
        """Generate arbiter activity patterns for testing"""
        self.log.debug(f"Generating {cycles} cycles of '{pattern}' activity{self.get_time_ns_str()}")

        # ✅ EXISTING PATTERNS (already implemented)
        if pattern == "random":
            await self._generate_random_activity(cycles)
        elif pattern == "starvation":
            await self._generate_starvation_pattern(cycles)
        elif pattern == "unfair":
            await self._generate_unfair_pattern(cycles)
        elif pattern == "performance":
            await self._generate_performance_pattern(cycles)
        elif pattern == "all_active":
            await self._generate_all_active_pattern(cycles)
        elif pattern == "single":
            await self._generate_single_client_pattern(cycles)
        elif pattern == "balanced":
            await self._generate_balanced_pattern(cycles)
        elif pattern == "ack_timeout":
            await self._generate_ack_timeout_pattern(cycles)
        elif pattern == "protocol_violation":
            await self._generate_protocol_violation_pattern(cycles)
        
        # ✅ THRESHOLD TEST PATTERNS (previously missing)
        elif pattern == "latency_stress":
            await self._generate_latency_stress_pattern(cycles)
        elif pattern == "inefficient":
            await self._generate_inefficient_pattern(cycles)
        elif pattern == "controlled":
            await self._generate_controlled_pattern(cycles)
        
        # ✅ BASIC TEST PATTERNS
        elif pattern == "mixed":
            await self._generate_mixed_pattern(cycles)
        
        # ✅ CORNER CASE TEST PATTERNS
        elif pattern.startswith("fill_cycle_"):
            cycle_num = int(pattern.split("_")[-1]) if pattern.split("_")[-1].isdigit() else 0
            await self._generate_fill_cycle_pattern(cycles, cycle_num)
        elif pattern == "pre_reset":
            await self._generate_pre_reset_pattern(cycles)
        elif pattern == "post_reset":
            await self._generate_post_reset_pattern(cycles)
        elif pattern.startswith("consistency_test_"):
            test_num = int(pattern.split("_")[-1]) if pattern.split("_")[-1].isdigit() else 0
            await self._generate_consistency_test_pattern(cycles, test_num)
        elif pattern == "stress":
            await self._generate_stress_pattern(cycles)
        elif pattern == "normal":
            await self._generate_normal_pattern(cycles)
        elif pattern.startswith("filter_"):
            filter_name = pattern.replace("filter_", "")
            await self._generate_filter_pattern(cycles, filter_name)
        
        # ✅ ERROR TEST PATTERNS
        elif pattern == "mixed_errors":
            await self._generate_mixed_errors_pattern(cycles)
        elif pattern == "controlled_errors":
            await self._generate_controlled_errors_pattern(cycles)
        
        # ✅ PERFORMANCE TEST PATTERNS
        elif pattern == "grant_focused":
            await self._generate_grant_focused_pattern(cycles)
        elif pattern == "ack_focused":
            await self._generate_ack_focused_pattern(cycles)
        elif pattern == "controlled_performance":
            await self._generate_controlled_performance_pattern(cycles)
        elif pattern == "high_throughput":
            await self._generate_high_throughput_pattern(cycles)
        elif pattern == "latency_focused":
            await self._generate_latency_focused_pattern(cycles)
        
        # ✅ STRESS TEST PATTERNS
        elif pattern.startswith("config_test_"):
            test_num = int(pattern.split("_")[-1]) if pattern.split("_")[-1].isdigit() else 0
            await self._generate_config_test_pattern(cycles, test_num)
        elif pattern.startswith("extended_cycle_"):
            cycle_num = int(pattern.split("_")[-1]) if pattern.split("_")[-1].isdigit() else 0
            await self._generate_extended_cycle_pattern(cycles, cycle_num)
        elif pattern == "rapid_cycle":
            await self._generate_rapid_cycle_pattern(cycles)
        elif pattern == "maximum_rate":
            await self._generate_maximum_rate_pattern(cycles)
        elif pattern.startswith("backpressure_"):
            level = int(pattern.split("_")[-1]) if pattern.split("_")[-1].isdigit() else 0
            await self._generate_backpressure_pattern(cycles, level)
        
        else:
            # ✅ FATAL ERROR INSTEAD OF SILENT FALLBACK
            valid_patterns = [
                "random", "starvation", "unfair", "performance", "all_active", "single", "balanced",
                "ack_timeout", "protocol_violation", "latency_stress", "inefficient", "controlled",
                "mixed", "fill_cycle_N", "pre_reset", "post_reset", "consistency_test_N", "stress",
                "normal", "filter_NAME", "mixed_errors", "controlled_errors", "grant_focused",
                "ack_focused", "controlled_performance", "high_throughput", "latency_focused",
                "config_test_N", "extended_cycle_N", "rapid_cycle", "maximum_rate", "backpressure_N"
            ]
            error_msg = f"❌ FATAL: Unknown activity pattern '{pattern}'\n" \
                    f"Valid patterns: {', '.join(valid_patterns)}"
            self.log.error(error_msg)
            raise ValueError(error_msg)

    # ========================================================================
    # NEW PATTERN IMPLEMENTATIONS
    # ========================================================================

    async def _generate_mixed_pattern(self, cycles: int):
        """Generate mixed activity for basic tests"""
        self.log.debug(f"Generating mixed pattern for {cycles} cycles")
        
        # Cycle through different activity types
        for i in range(cycles):
            cycle_type = i % 4
            
            if cycle_type == 0:
                # Random activity
                req_mask = random.randint(0, (1 << self.clients) - 1)
            elif cycle_type == 1:
                # High activity
                req_mask = (1 << self.clients) - 1  # All clients
            elif cycle_type == 2:
                # Single client
                req_mask = 1 << (i % self.clients)
            else:
                # Moderate activity
                req_mask = random.randint(1, (1 << min(4, self.clients)) - 1)
            
            self.dut.request.value = req_mask
            await self._simulate_ideal_grant(req_mask)
            await self.wait_clocks('clk', 1)

    async def _generate_fill_cycle_pattern(self, cycles: int, cycle_num: int):
        """Generate patterns for FIFO fill testing"""
        self.log.debug(f"Generating fill cycle {cycle_num} pattern for {cycles} cycles")
        
        # Vary intensity based on cycle number
        intensity = min(0.9, 0.3 + (cycle_num * 0.2))
        
        for i in range(cycles):
            if random.random() < intensity:
                req_mask = random.randint(1, (1 << self.clients) - 1)
            else:
                req_mask = 0
            
            self.dut.request.value = req_mask
            await self._simulate_ideal_grant(req_mask)
            await self.wait_clocks('clk', 1)

    async def _generate_pre_reset_pattern(self, cycles: int):
        """Generate activity before reset testing"""
        self.log.debug(f"Generating pre-reset pattern for {cycles} cycles")
        
        for i in range(cycles):
            # Gradually increase activity leading to reset
            intensity = i / cycles
            if random.random() < intensity:
                req_mask = random.randint(1, (1 << self.clients) - 1)
            else:
                req_mask = 0
            
            self.dut.request.value = req_mask
            await self._simulate_ideal_grant(req_mask)
            await self.wait_clocks('clk', 1)

    async def _generate_post_reset_pattern(self, cycles: int):
        """Generate activity after reset testing"""
        self.log.debug(f"Generating post-reset pattern for {cycles} cycles")
        
        for i in range(cycles):
            # Gradually ramp up activity after reset
            intensity = min(0.8, i / (cycles * 0.5))
            if random.random() < intensity:
                req_mask = random.randint(1, (1 << self.clients) - 1)
            else:
                req_mask = 0
            
            self.dut.request.value = req_mask
            await self._simulate_ideal_grant(req_mask)
            await self.wait_clocks('clk', 1)

    async def _generate_consistency_test_pattern(self, cycles: int, test_num: int):
        """Generate consistent patterns for configuration testing"""
        self.log.debug(f"Generating consistency test {test_num} pattern for {cycles} cycles")
        
        # Use test_num to create different but repeatable patterns
        random.seed(42 + test_num)  # Deterministic seed
        
        for i in range(cycles):
            req_mask = random.randint(1, (1 << self.clients) - 1)
            self.dut.request.value = req_mask
            await self._simulate_ideal_grant(req_mask)
            await self.wait_clocks('clk', 1)
        
        random.seed()  # Reset to random seed

    async def _generate_stress_pattern(self, cycles: int):
        """Generate high-stress activity patterns"""
        self.log.debug(f"Generating stress pattern for {cycles} cycles")
        
        for i in range(cycles):
            # Maximum activity most of the time
            if random.random() < 0.9:
                req_mask = (1 << self.clients) - 1  # All clients
            else:
                req_mask = random.randint(1, (1 << self.clients) - 1)
            
            self.dut.request.value = req_mask
            await self._simulate_ideal_grant(req_mask)
            await self.wait_clocks('clk', 1)

    async def _generate_normal_pattern(self, cycles: int):
        """Generate normal operational patterns"""
        self.log.debug(f"Generating normal pattern for {cycles} cycles")
        
        for i in range(cycles):
            # Moderate activity with realistic distribution
            if random.random() < 0.6:
                req_mask = random.randint(1, (1 << min(3, self.clients)) - 1)
            elif random.random() < 0.2:
                req_mask = 0  # Idle periods
            else:
                req_mask = random.randint(1, (1 << self.clients) - 1)
            
            self.dut.request.value = req_mask
            await self._simulate_ideal_grant(req_mask)
            await self.wait_clocks('clk', 1)

    async def _generate_filter_pattern(self, cycles: int, filter_name: str):
        """Generate patterns for filter testing"""
        self.log.debug(f"Generating filter '{filter_name}' pattern for {cycles} cycles")
        
        # Pattern varies based on filter name
        for i in range(cycles):
            if "high" in filter_name.lower():
                req_mask = (1 << self.clients) - 1  # All active
            elif "low" in filter_name.lower():
                req_mask = random.randint(0, 3)  # Low activity
            elif "single" in filter_name.lower():
                req_mask = 1 << (i % self.clients)  # Single client
            else:
                req_mask = random.randint(1, (1 << self.clients) - 1)
            
            self.dut.request.value = req_mask
            await self._simulate_ideal_grant(req_mask)
            await self.wait_clocks('clk', 1)

    async def _generate_controlled_errors_pattern(self, cycles: int):
        """Generate controlled error patterns"""
        self.log.debug(f"Generating controlled errors pattern for {cycles} cycles")
        
        # Deliberately create specific error conditions in sequence
        phase_length = cycles // 4
        
        for i in range(cycles):
            phase = i // phase_length
            
            if phase == 0:  # Starvation phase
                req_mask = 0x1  # Only client 0
                grant_mask = 0x1
            elif phase == 1:  # Timeout phase
                req_mask = random.randint(1, (1 << self.clients) - 1)
                grant_mask = req_mask  # Grant but don't ACK
            elif phase == 2:  # Unfairness phase
                req_mask = (1 << self.clients) - 1
                grant_mask = 0x1  # Always favor client 0
            else:  # Protocol violation phase
                req_mask = random.randint(1, (1 << self.clients) - 1)
                grant_mask = req_mask
                # Add spurious ACKs
                if random.random() < 0.3:
                    spurious_ack = random.randint(1, (1 << self.clients) - 1)
                    self.dut.grant_ack.value = spurious_ack
                    await self.wait_clocks('clk', 1)
                    self.dut.grant_ack.value = 0
            
            self.dut.request.value = req_mask
            await self._simulate_controlled_grant(grant_mask)
            await self.wait_clocks('clk', 1)

    async def _generate_ack_focused_pattern(self, cycles: int):
        """Generate patterns focused on ACK behavior"""
        self.log.debug(f"Generating ACK-focused pattern for {cycles} cycles")
        
        for i in range(cycles):
            req_mask = random.randint(1, (1 << self.clients) - 1)
            self.dut.request.value = req_mask
            
            # Always grant and focus on ACK timing
            await self._simulate_ideal_grant(req_mask)
            
            if self.wait_gnt_ack and self.grant_active:
                # Vary ACK timing for testing
                if i % 3 == 0:
                    await self._simulate_immediate_ack()
                elif i % 3 == 1:
                    await self._simulate_delayed_acks()
                else:
                    await self._simulate_random_acks()
            
            await self.wait_clocks('clk', 1)

    async def _generate_controlled_performance_pattern(self, cycles: int):
        """Generate controlled performance patterns"""
        self.log.debug(f"Generating controlled performance pattern for {cycles} cycles")
        
        for i in range(cycles):
            # Create specific performance scenarios
            scenario = i % 5
            
            if scenario == 0:  # High throughput
                req_mask = (1 << self.clients) - 1
            elif scenario == 1:  # Bursty
                req_mask = (1 << self.clients) - 1 if i % 4 < 2 else 0
            elif scenario == 2:  # Single client focus
                req_mask = 1 << (i % self.clients)
            elif scenario == 3:  # Moderate load
                req_mask = random.randint(1, (1 << (self.clients // 2)) - 1)
            else:  # Random
                req_mask = random.randint(0, (1 << self.clients) - 1)
            
            self.dut.request.value = req_mask
            await self._simulate_ideal_grant(req_mask)
            await self.wait_clocks('clk', 1)

    async def _generate_high_throughput_pattern(self, cycles: int):
        """Generate maximum throughput patterns"""
        self.log.debug(f"Generating high throughput pattern for {cycles} cycles")
        
        for i in range(cycles):
            # Maximum activity with optimal ACK timing
            req_mask = (1 << self.clients) - 1  # All clients always requesting
            self.dut.request.value = req_mask
            
            await self._simulate_ideal_grant(req_mask)
            
            # Immediate ACKs for maximum throughput
            if self.wait_gnt_ack and self.grant_active:
                await self._simulate_immediate_ack()
            
            await self.wait_clocks('clk', 1)

    async def _generate_latency_focused_pattern(self, cycles: int):
        """Generate patterns for latency testing"""
        self.log.debug(f"Generating latency-focused pattern for {cycles} cycles")
        
        for i in range(cycles):
            # Create latency stress by delaying grants
            req_mask = random.randint(1, (1 << self.clients) - 1)
            self.dut.request.value = req_mask
            
            # Grant only every Nth cycle to build latency
            if i % 3 == 0:
                await self._simulate_ideal_grant(req_mask)
            else:
                # No grant - build up latency
                self.dut.grant_valid.value = 0
                self.dut.grant.value = 0
                self.dut.grant_id.value = 0
            
            await self.wait_clocks('clk', 1)

    async def _generate_config_test_pattern(self, cycles: int, test_num: int):
        """Generate patterns for configuration testing"""
        self.log.debug(f"Generating config test {test_num} pattern for {cycles} cycles")
        
        # Different patterns based on test number
        intensity = 0.3 + (test_num % 5) * 0.15  # Vary from 30% to 90%
        
        for i in range(cycles):
            if random.random() < intensity:
                req_mask = random.randint(1, (1 << self.clients) - 1)
            else:
                req_mask = 0
            
            self.dut.request.value = req_mask
            await self._simulate_ideal_grant(req_mask)
            await self.wait_clocks('clk', 1)

    async def _generate_extended_cycle_pattern(self, cycles: int, cycle_num: int):
        """Generate patterns for extended operation testing"""
        self.log.debug(f"Generating extended cycle {cycle_num} pattern for {cycles} cycles")
        
        # Vary behavior across extended cycles
        base_pattern = cycle_num % 4
        
        for i in range(cycles):
            if base_pattern == 0:
                req_mask = random.randint(1, (1 << self.clients) - 1)
            elif base_pattern == 1:
                req_mask = (1 << self.clients) - 1  # All active
            elif base_pattern == 2:
                req_mask = 1 << (i % self.clients)  # Round robin
            else:
                req_mask = random.randint(0, (1 << (self.clients // 2)) - 1)
            
            self.dut.request.value = req_mask
            await self._simulate_ideal_grant(req_mask)
            await self.wait_clocks('clk', 1)

    async def _generate_rapid_cycle_pattern(self, cycles: int):
        """Generate rapid cycling patterns"""
        self.log.debug(f"Generating rapid cycle pattern for {cycles} cycles")
        
        for i in range(cycles):
            # Rapidly changing request patterns
            req_mask = 1 << (i % self.clients)  # Rapidly cycle through clients
            self.dut.request.value = req_mask
            await self._simulate_ideal_grant(req_mask)
            # No wait - maximum rate
            await self.wait_clocks('clk', 1)

    async def _generate_maximum_rate_pattern(self, cycles: int):
        """Generate maximum rate patterns"""
        self.log.debug(f"Generating maximum rate pattern for {cycles} cycles")
        
        for i in range(cycles):
            # Always all clients requesting for maximum load
            req_mask = (1 << self.clients) - 1
            self.dut.request.value = req_mask
            await self._simulate_ideal_grant(req_mask)
            
            # Immediate ACKs for maximum rate
            if self.wait_gnt_ack and self.grant_active:
                await self._simulate_immediate_ack()
            
            await self.wait_clocks('clk', 1)

    async def _generate_backpressure_pattern(self, cycles: int, level: int):
        """Generate patterns with varying backpressure"""
        self.log.debug(f"Generating backpressure level {level} pattern for {cycles} cycles")
        
        # Set MonBus ready probability based on backpressure level
        ready_prob = max(0.1, 1.0 - (level * 0.2))  # Level 0=100%, Level 4=20%
        if hasattr(self.monbus_slave, 'set_ready_probability'):
            self.monbus_slave.set_ready_probability(ready_prob)
        
        for i in range(cycles):
            req_mask = random.randint(1, (1 << self.clients) - 1)
            self.dut.request.value = req_mask
            await self._simulate_ideal_grant(req_mask)
            await self.wait_clocks('clk', 1)
        
        # Restore full ready
        if hasattr(self.monbus_slave, 'set_ready_probability'):
            self.monbus_slave.set_ready_probability(1.0)

    # ========================================================================
    # HELPER METHODS FOR PATTERN IMPLEMENTATIONS
    # ========================================================================

    async def _simulate_ideal_grant(self, req_mask: int):
        """Simulate ideal arbiter granting to first requesting client"""
        if req_mask != 0:
            # Find first requesting client
            for client in range(self.clients):
                if req_mask & (1 << client):
                    self.dut.grant_valid.value = 1
                    self.dut.grant.value = 1 << client
                    self.dut.grant_id.value = client
                    self.last_grant_id = client
                    self.grant_active = True
                    break
        else:
            self.dut.grant_valid.value = 0
            self.dut.grant.value = 0
            self.dut.grant_id.value = 0

    async def _simulate_controlled_grant(self, grant_mask: int):
        """Simulate controlled grant behavior"""
        if grant_mask != 0:
            # Find first granted client
            for client in range(self.clients):
                if grant_mask & (1 << client):
                    self.dut.grant_valid.value = 1
                    self.dut.grant.value = grant_mask
                    self.dut.grant_id.value = client
                    self.last_grant_id = client
                    self.grant_active = True
                    break
        else:
            self.dut.grant_valid.value = 0
            self.dut.grant.value = 0
            self.dut.grant_id.value = 0

    async def _simulate_immediate_ack(self):
        """Simulate immediate ACK response"""
        if self.grant_active:
            ack_mask = 1 << self.last_grant_id
            self.dut.grant_ack.value = ack_mask
            await self.wait_clocks('clk', 1)
            self.dut.grant_ack.value = 0
            self.grant_active = False

    async def _generate_latency_stress_pattern(self, cycles: int):
        """Generate patterns that stress latency monitoring - delays grants deliberately"""
        self.log.debug(f"Generating latency stress pattern for {cycles} cycles")
        
        for i in range(cycles):
            # Generate requests but delay grants to build up latency
            req_mask = random.randint(1, (1 << self.clients) - 1)
            self.dut.request.value = req_mask
            
            # Only grant occasionally to build up request latency
            if i % 5 == 0:  # Grant every 5th cycle to create latency buildup
                # Find first requesting client
                for client in range(self.clients):
                    if req_mask & (1 << client):
                        self.dut.grant_valid.value = 1
                        self.dut.grant.value = 1 << client
                        self.dut.grant_id.value = client
                        break
            else:
                # No grants - let latency build up
                self.dut.grant_valid.value = 0
                self.dut.grant.value = 0
                self.dut.grant_id.value = 0
            
            # Simulate ACKs if needed
            if self.wait_gnt_ack and random.random() < 0.8:
                await self._simulate_random_acks()
            
            await self.wait_clocks('clk', 1)

    async def _generate_inefficient_pattern(self, cycles: int):
        """Generate patterns that create inefficient grant usage"""
        self.log.debug(f"Generating inefficient pattern for {cycles} cycles")
        
        for i in range(cycles):
            # Generate many grants but simulate poor ACK completion rates
            req_mask = random.randint(1, (1 << self.clients) - 1)
            self.dut.request.value = req_mask
            
            # Always try to grant to first requesting client
            for client in range(self.clients):
                if req_mask & (1 << client):
                    self.dut.grant_valid.value = 1
                    self.dut.grant.value = 1 << client
                    self.dut.grant_id.value = client
                    self.last_grant_id = client
                    self.grant_active = True
                    break
            
            # Make ACK completion very poor (only 40% completion rate)
            if self.wait_gnt_ack and self.grant_active and random.random() < 0.4:
                # Send ACK for granted client
                ack_mask = 1 << self.last_grant_id
                self.dut.grant_ack.value = ack_mask
                await self.wait_clocks('clk', 1)
                self.dut.grant_ack.value = 0
                self.grant_active = False
            
            await self.wait_clocks('clk', 1)

    async def _generate_controlled_pattern(self, cycles: int):
        """Generate controlled, predictable patterns for testing specific conditions"""
        self.log.debug(f"Generating controlled pattern for {cycles} cycles")
        
        # Phase 1: Build up starvation for high-numbered clients
        starvation_cycles = cycles // 3
        for i in range(starvation_cycles):
            # Only clients 0 and 1 get requests and grants
            req_mask = 0x3  # Clients 0 and 1 only
            self.dut.request.value = req_mask
            
            # Always grant to client 0 to starve client 1
            self.dut.grant_valid.value = 1
            self.dut.grant.value = 0x1  # Only client 0
            self.dut.grant_id.value = 0
            
            await self.wait_clocks('clk', 1)
        
        # Phase 2: All clients active (high activity threshold)
        active_cycles = cycles // 3
        for i in range(active_cycles):
            # All clients requesting
            req_mask = (1 << self.clients) - 1
            self.dut.request.value = req_mask
            
            # Grant to round-robin but slowly
            grant_client = i % self.clients
            self.dut.grant_valid.value = 1
            self.dut.grant.value = 1 << grant_client
            self.dut.grant_id.value = grant_client
            
            await self.wait_clocks('clk', 2)  # Slower granting
        
        # Phase 3: Return to normal operation
        remaining_cycles = cycles - starvation_cycles - active_cycles
        await self._generate_random_activity(remaining_cycles)

    async def _generate_mixed_errors_pattern(self, cycles: int):
        """Generate patterns that create multiple types of errors simultaneously"""
        self.log.debug(f"Generating mixed errors pattern for {cycles} cycles")
        
        for i in range(cycles):
            cycle_type = i % 6  # Rotate through different error types
            
            if cycle_type == 0:  # Starvation
                req_mask = 0x1  # Only client 0
                grant_mask = 0x1
                grant_id = 0
            elif cycle_type == 1:  # High activity
                req_mask = (1 << self.clients) - 1  # All clients
                grant_mask = 0x1  # But only grant to one
                grant_id = 0
            elif cycle_type == 2:  # Unfairness
                req_mask = 0xF  # First 4 clients
                grant_mask = 0x1  # Always client 0
                grant_id = 0
            elif cycle_type == 3:  # Latency stress
                req_mask = random.randint(1, (1 << self.clients) - 1)
                grant_mask = 0  # No grants to build latency
                grant_id = 0
            elif cycle_type == 4:  # Protocol violations
                req_mask = random.randint(1, (1 << self.clients) - 1)
                grant_mask = random.randint(1, (1 << self.clients) - 1)  # Grant to requesting client
                grant_id = 0
                # Add spurious ACK
                if random.random() < 0.2:
                    spurious_ack = random.randint(1, (1 << self.clients) - 1)
                    self.dut.grant_ack.value = spurious_ack
                    await self.wait_clocks('clk', 1)
                    self.dut.grant_ack.value = 0
            else:  # Normal operation
                req_mask = random.randint(1, (1 << self.clients) - 1)
                grant_mask = req_mask & (req_mask ^ (req_mask - 1))  # Grant to first requesting
                grant_id = 0
                for j in range(self.clients):
                    if grant_mask & (1 << j):
                        grant_id = j
                        break
            
            self.dut.request.value = req_mask
            self.dut.grant_valid.value = 1 if grant_mask != 0 else 0
            self.dut.grant.value = grant_mask
            self.dut.grant_id.value = grant_id
            
            # Poor ACK completion for inefficiency
            if self.wait_gnt_ack and grant_mask != 0 and random.random() < 0.5:
                await self._simulate_delayed_acks()
            
            await self.wait_clocks('clk', 1)

    async def _generate_grant_focused_pattern(self, cycles: int):
        """Generate patterns focused on grant event tracking"""
        self.log.debug(f"Generating grant-focused pattern for {cycles} cycles")
        
        for i in range(cycles):
            # Ensure high grant activity for tracking
            req_mask = random.randint(1, (1 << min(4, self.clients)) - 1)
            self.dut.request.value = req_mask
            
            # Always grant to someone if there are requests
            if req_mask != 0:
                # Grant to first requesting client
                for client in range(self.clients):
                    if req_mask & (1 << client):
                        self.dut.grant_valid.value = 1
                        self.dut.grant.value = 1 << client
                        self.dut.grant_id.value = client
                        self.last_grant_id = client
                        self.grant_active = True
                        break
            else:
                self.dut.grant_valid.value = 0
                self.dut.grant.value = 0
                self.dut.grant_id.value = 0
            
            # High ACK completion rate for this pattern
            if self.wait_gnt_ack and self.grant_active and random.random() < 0.9:
                # Quick ACK response
                ack_mask = 1 << self.last_grant_id
                self.dut.grant_ack.value = ack_mask
                await self.wait_clocks('clk', 1)
                self.dut.grant_ack.value = 0
                self.grant_active = False
            
            await self.wait_clocks('clk', 1)

    async def _generate_random_activity(self, cycles: int):
        """Generate random request patterns with ACK simulation"""
        for i in range(cycles):
            # Random subset of clients request
            req_mask = random.randint(0, (1 << self.clients) - 1)
            self.dut.request.value = req_mask

            # Simulate ACKs with some probability
            if self.wait_gnt_ack and random.random() < 0.8:
                await self._simulate_random_acks()

            await self.wait_clocks('clk', 1)

    async def _generate_starvation_pattern(self, cycles: int):
        """Generate patterns that cause starvation"""
        # Favor lower-numbered clients heavily
        for i in range(cycles):
            # 80% chance for client 0, 15% for client 1, 5% for others
            rand = random.random()
            if rand < 0.8:
                req_mask = 1  # Only client 0
            elif rand < 0.95:
                req_mask = 3  # Clients 0 and 1
            else:
                req_mask = random.randint(1, (1 << self.clients) - 1)

            self.dut.request.value = req_mask

            # Simulate ACKs
            if self.wait_gnt_ack and random.random() < 0.7:
                await self._simulate_delayed_acks()

            await self.wait_clocks('clk', 1)

    async def _generate_ack_timeout_pattern(self, cycles: int):
        """Generate patterns that cause ACK timeouts"""
        for i in range(cycles):
            req_mask = random.randint(1, (1 << self.clients) - 1)
            self.dut.request.value = req_mask

            # Deliberately don't send ACKs to cause timeouts
            if self.wait_gnt_ack and random.random() < 0.3:  # Only 30% ACK rate
                await self._simulate_random_acks()

            await self.wait_clocks('clk', 1)

    async def _generate_protocol_violation_pattern(self, cycles: int):
        """Generate patterns that might cause protocol violations"""
        for i in range(cycles):
            req_mask = random.randint(1, (1 << self.clients) - 1)
            self.dut.request.value = req_mask

            # Occasionally send spurious ACKs
            if random.random() < 0.1:
                spurious_ack = random.randint(1, (1 << self.clients) - 1)
                self.dut.grant_ack.value = spurious_ack
                await self.wait_clocks('clk', 1)
                self.dut.grant_ack.value = 0

            await self.wait_clocks('clk', 1)

    async def _simulate_random_acks(self):
        """Simulate ACK responses with random timing"""
        if self.grant_active:
            # Random delay before ACK
            delay = random.randint(1, 5)
            await self.wait_clocks('clk', delay)

            # Send ACK for granted client
            ack_mask = 1 << self.last_grant_id
            self.dut.grant_ack.value = ack_mask
            await self.wait_clocks('clk', 1)
            self.dut.grant_ack.value = 0

    async def _simulate_delayed_acks(self):
        """Simulate delayed ACK responses"""
        if self.grant_active:
            # Longer delay to stress the system
            delay = random.randint(5, 15)
            await self.wait_clocks('clk', delay)

            # Send ACK for granted client
            ack_mask = 1 << self.last_grant_id
            self.dut.grant_ack.value = ack_mask
            await self.wait_clocks('clk', 1)
            self.dut.grant_ack.value = 0

    async def _generate_starvation_pattern(self, cycles: int):
        """Generate patterns that cause starvation"""
        # Favor lower-numbered clients heavily
        for i in range(cycles):
            # 80% chance for client 0, 15% for client 1, 5% for others
            rand = random.random()
            if rand < 0.8:
                req_mask = 1  # Only client 0
            elif rand < 0.95:
                req_mask = 3  # Clients 0 and 1
            else:
                req_mask = random.randint(1, (1 << self.clients) - 1)

            self.dut.request.value = req_mask
            await self.wait_clocks('clk', 1)

    async def _generate_unfair_pattern(self, cycles: int):
        """Generate unfair request patterns"""
        # Similar to starvation but more varied
        for i in range(cycles):
            # Heavily favor first half of clients
            if random.random() < 0.7:
                max_client = min(4, self.clients // 2)
                req_mask = random.randint(1, (1 << max_client) - 1)
            else:
                req_mask = random.randint(1, (1 << self.clients) - 1)

            self.dut.request.value = req_mask
            await self.wait_clocks('clk', 1)

    async def _generate_performance_pattern(self, cycles: int):
        """Generate patterns for performance testing"""
        for i in range(cycles):
            # Moderate activity with some bursts
            if i % 10 < 7:  # 70% activity
                req_mask = random.randint(1, (1 << min(4, self.clients)) - 1)
            else:  # 30% idle or light activity
                req_mask = random.randint(0, 1)

            self.dut.request.value = req_mask
            await self.wait_clocks('clk', 1)

    async def _generate_all_active_pattern(self, cycles: int):
        """Generate patterns where all clients are often active"""
        for i in range(cycles):
            # High probability of many clients active
            if random.random() < 0.8:
                req_mask = (1 << self.clients) - 1  # All clients
            else:
                req_mask = random.randint((1 << (self.clients - 2)), (1 << self.clients) - 1)

            self.dut.request.value = req_mask
            await self.wait_clocks('clk', 1)

    async def _generate_single_client_pattern(self, cycles: int):
        """Generate single client activity pattern"""
        for i in range(cycles):
            # Rotate through clients
            active_client = i % self.clients
            req_mask = 1 << active_client
            self.dut.request.value = req_mask
            await self.wait_clocks('clk', 2)  # Hold for 2 cycles

    async def _generate_balanced_pattern(self, cycles: int):
        """Generate balanced activity across all clients"""
        for i in range(cycles):
            # Round-robin with some randomness
            if i % 4 == 0:  # Every 4th cycle, random activity
                req_mask = random.randint(1, (1 << self.clients) - 1)
            else:
                # Sequential client activation
                active_client = i % self.clients
                req_mask = 1 << active_client

            self.dut.request.value = req_mask
            await self.wait_clocks('clk', 1)

    # =================================================================
    # TEST EXECUTION METHODS - CALLS THE IMPORTED TEST CLASSES
    # =================================================================

    async def run_tests(self) -> bool:
        """Run tests using new framework (minimal changes to your existing logic)"""
        
        # Ensure setup is complete (your existing pattern)
        if not hasattr(self, 'monbus_slave') or self.monbus_slave is None:
            self.log.info("Setting up testbench...")
            await self.setup_testbench()
        
        # Use new framework for filtering instead of your existing logic
        if self.test_framework:
            compatible_tests, skipped_tests = self.test_framework.get_compatible_tests(self.test_level)
        else:
            # Fallback to your existing method if framework not ready
            compatible_tests, skipped_tests = self.test_registry.get_compatible_tests(self.config, self.test_level)
        
        self.log.info(f"=== Running {len(compatible_tests)} tests for '{self.test_level}' level ===")
        
        if skipped_tests:
            self.log.info(f"Skipping {len(skipped_tests)} incompatible tests:")
            for test_name, reason in skipped_tests:
                self.log.info(f"  {test_name}: SKIPPED - {reason}")
        
        # Execute tests (keep your existing execution pattern)
        results = {}
        for test_name in compatible_tests:
            self.log.info(f"Running test: {test_name}")
            try:
                # Try new framework first, fallback to existing method
                if self.test_framework:
                    test_method = self.test_framework.get_test_method(test_name)
                    if test_method:
                        result = await test_method()
                    else:
                        result = await self._execute_test(test_name)  # Your existing method
                else:
                    result = await self._execute_test(test_name)  # Your existing method
                
                results[test_name] = result.passed
                if not result.passed:
                    self.log.error(f"{test_name}: ❌ FAIL - {result.details}")
            except Exception as e:
                self.log.error(f"{test_name}: ❌ EXCEPTION - {str(e)}")
                results[test_name] = False
        
        # Keep your existing result storage and printing
        self.test_results[self.test_level] = results
        self._print_test_summary(compatible_tests, skipped_tests, results)
        
        return all(results.values())

    async def _execute_test(self, test_name: str) -> TestResult:
        """Execute a single test - FIXED method names"""
        
        # CORRECTED method mapping (this was the main bug)
        test_methods = {
            'monitor_enable_disable': self.basic_test.test_monitor_enable_disable,
            'packet_generation': self.basic_test.test_packet_generation,
            'packet_filtering': self.basic_test.test_packet_type_filtering,
            'protocol_filtering': self.basic_test.test_protocol_filtering,
            'latency_thresholds': self.threshold_test.test_latency_thresholds,
            'starvation_thresholds': self.threshold_test.test_starvation_thresholds,
            'fairness_thresholds': self.threshold_test.test_fairness_thresholds,
            'active_thresholds': self.threshold_test.test_active_request_thresholds,
            'starvation_errors': self.error_test.test_starvation_error_detection,
            'ack_timeout': self.error_test.test_ack_timeout_detection,
            'performance_events': self.performance_test.test_performance_event_generation,
            'grant_tracking': self.performance_test.test_grant_tracking,
            'ack_tracking': self.performance_test.test_ack_tracking,
            'protocol_violations': self.error_test.test_protocol_violation_detection,
            'fairness_violations': self.error_test.test_fairness_violation_detection,
            'multiple_errors': self.error_test.test_multiple_error_types,
            'efficiency_thresholds': self.threshold_test.test_efficiency_thresholds,
            'threshold_data': self.threshold_test.test_threshold_packet_data,
            'fifo_stress': self.stress_test.test_fifo_overflow_handling,
            'config_stability': self.stress_test.test_configuration_stability,
            'extended_operation': self.stress_test.test_extended_operation,
            'fifo_exactly_full': self.fifo_corner_test.test_fifo_exactly_full,
            'fifo_rapid_cycles': self.fifo_corner_test.test_fifo_rapid_fill_drain,
            'reset_during_op': self.reset_behavior_test.test_reset_during_operation,
            'minimal_thresholds': self.config_edge_test.test_minimal_threshold_values,
        }
        
        if test_name not in test_methods:
            error_msg = f"Unknown test: {test_name}"
            self.log.error(error_msg)
            return TestResult(passed=False, name=test_name, details=error_msg, error_msg=error_msg)
            
        try:
            result = await test_methods[test_name]()
            status = "✅ PASS" if result.passed else "❌ FAIL"
            self.log.info(f"=== {test_name}: {status} ===")
            return result
        except Exception as e:
            error_msg = f"Exception in {test_name}: {str(e)}"
            self.log.error(error_msg)
            return TestResult(passed=False, name=test_name, details=error_msg, error_msg=str(e))

    def _print_test_summary(self, compatible_tests, skipped_tests, results):
        """Print clean test summary"""
        
        passed_count = sum(1 for test in compatible_tests if results[test])
        total_compatible = len(compatible_tests)
        
        self.log.info("=" * 60)
        self.log.info("TEST SUMMARY")
        self.log.info("=" * 60)
        self.log.info(f"{self.test_level.upper()}: {passed_count}/{total_compatible} passed")
        
        for test_name in compatible_tests:
            status = "✅ PASS" if results[test_name] else "❌ FAIL"
            self.log.info(f"  {test_name}: {status}")
        
        if skipped_tests:
            self.log.info(f"SKIPPED: {len(skipped_tests)} tests (incompatible with current configuration)")
            for test_name, reason in skipped_tests:
                self.log.info(f"  {test_name}: SKIPPED - {reason}")
        
        self.log.info("=" * 60)
        self.log.info(f"Configuration: {self.config}")

    def print_test_summary(self):
        """Print comprehensive test summary"""
        self.log.info("=" * 60)
        self.log.info("TEST SUMMARY")
        self.log.info("=" * 60)

        if not self.test_results:
            self.log.warning("No test results available")
            return

        total_tests = 0
        passed_tests = 0

        for category, results in self.test_results.items():
            category_total = len(results) if isinstance(results, dict) else 0
            category_passed = sum(results.values()) if isinstance(results, dict) else 0

            self.log.info(f"{category.upper()}: {category_passed}/{category_total} passed")

            if isinstance(results, dict):
                for test_name, passed in results.items():
                    status = "✅ PASS" if passed else "❌ FAIL"
                    self.log.info(f"  {test_name}: {status}")

            total_tests += category_total
            passed_tests += category_passed

        self.log.info("=" * 60)
        success_rate = (passed_tests / total_tests) * 100 if total_tests > 0 else 0
        self.log.info(f"OVERALL: {passed_tests}/{total_tests} ({success_rate:.1f}%)")
        self.log.info("=" * 60)

    def get_failure_summary(self):
        """Get a summary of failed tests"""
        failed_tests = []

        for level, results in self.test_results.items():
            for test_name, passed in results.items():
                if not passed:
                    failed_tests.append(f"{level}.{test_name}")

        return failed_tests
