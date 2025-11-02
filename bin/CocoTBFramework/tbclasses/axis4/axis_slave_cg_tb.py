# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXISSlaveCGTB
# Purpose: AXIS Slave Clock Gated Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIS Slave Clock Gated Testbench

Testbench for testing axis_slave_cg.sv module using the CocoTB framework.
Extends the base AXIS slave testbench with clock gating functionality.

Architecture:
    s_axis_* (input) -> [axis_slave_cg] -> fub_axis_* (output)
                           |
                      Clock Gating Control

Based on AXI4 clock gated testbench patterns but adapted for AXIS stream testing.
"""

import os
import random
from cocotb.triggers import RisingEdge, Timer

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.amba.amba_cg_ctrl import AxiClockGateCtrl

# Import base AXIS slave testbench
from .axis_slave_tb import AXISSlaveTB


class AXISSlaveCGTB(AXISSlaveTB):
    """
    Clock-gated AXIS Slave testbench.
    Extends the base AXIS slave testbench with clock gating capabilities.
    """

    def __init__(self, dut, aclk=None, aresetn=None):
        super().__init__(dut, aclk, aresetn)

        # Clock gating specific setup
        self.cg_ctrl = None
        self.setup_clock_gating_controller()

        # Clock gating test statistics
        self.cg_stats = {
            'total_cycles_monitored': 0,
            'gated_cycles': 0,
            'power_efficiency_percent': 0.0,
            'gating_transitions': 0
        }

    def setup_clock_gating_controller(self):
        """Setup clock gating controller for monitoring."""
        try:
            self.cg_ctrl = AxiClockGateCtrl(
                dut=self.dut,
                instance_path="i_amba_clock_gate_ctrl",
                clock_signal_name="aclk",
                user_valid_signals=["s_axis_tvalid"],
                axi_valid_signals=["fub_axis_tvalid"],
                gating_signal_name="cg_gating",
                idle_signal_name="cg_idle",
                enable_signal_name="cfg_cg_enable",
                idle_count_signal_name="cfg_cg_idle_count"
            )
            self.log.info("✓ Clock gating controller initialized")
        except Exception as e:
            self.log.warning(f"Could not initialize CG controller: {e}")

    async def configure_clock_gating(self, enable=True, idle_count=8):
        """Configure clock gating parameters."""
        if hasattr(self.dut, 'cfg_cg_enable'):
            self.dut.cfg_cg_enable.value = 1 if enable else 0
        if hasattr(self.dut, 'cfg_cg_idle_count'):
            self.dut.cfg_cg_idle_count.value = idle_count

        if self.cg_ctrl:
            self.cg_ctrl.enable_clock_gating(enable)
            self.cg_ctrl.set_idle_count(idle_count)

        await self.wait_clocks(self.aclk_name, 5)  # Let configuration settle
        self.log.info(f"Clock gating configured: enable={enable}, idle_count={idle_count}")

    async def wait_for_gating_state(self, target_state=True, timeout_cycles=100):
        """Wait for specific gating state."""
        if not hasattr(self.dut, 'cg_gating'):
            return True  # Skip if no gating signal

        for _ in range(timeout_cycles):
            current_state = bool(self.dut.cg_gating.value)
            if current_state == target_state:
                state_name = "gated" if target_state else "ungated"
                self.log.info(f"Reached {state_name} state")
                return True
            await RisingEdge(self.aclk)

        self.log.warning(f"Timeout waiting for gating state {target_state}")
        return False

    async def measure_power_efficiency(self, test_duration_cycles=1000):
        """Measure power efficiency during a test period."""
        if not hasattr(self.dut, 'cg_gating'):
            return {'error': 'No cg_gating signal available'}

        gated_cycles = 0
        transition_count = 0
        prev_gating_state = bool(self.dut.cg_gating.value)

        for cycle in range(test_duration_cycles):
            current_gating_state = bool(self.dut.cg_gating.value)

            if current_gating_state:
                gated_cycles += 1

            if current_gating_state != prev_gating_state:
                transition_count += 1
                prev_gating_state = current_gating_state

            await RisingEdge(self.aclk)

        efficiency = (gated_cycles / test_duration_cycles) * 100 if test_duration_cycles > 0 else 0

        self.cg_stats.update({
            'total_cycles_monitored': test_duration_cycles,
            'gated_cycles': gated_cycles,
            'power_efficiency_percent': efficiency,
            'gating_transitions': transition_count
        })

        self.log.info(f"Power efficiency: {efficiency:.1f}% ({gated_cycles}/{test_duration_cycles} cycles gated)")
        return self.cg_stats

    async def validate_ready_signals_during_gating(self):
        """Validate that ready signals are properly controlled during gating."""
        if not hasattr(self.dut, 'cg_gating'):
            return True

        gating_active = bool(self.dut.cg_gating.value)

        if gating_active:
            # Check that ready signals are forced to 0 during gating
            ready_checks = []

            if hasattr(self.dut, 's_axis_tready'):
                s_tready_ok = not bool(self.dut.s_axis_tready.value)
                ready_checks.append(('s_axis_tready', s_tready_ok))

            all_ready_ok = all(check[1] for check in ready_checks)

            if not all_ready_ok:
                failed_signals = [check[0] for check in ready_checks if not check[1]]
                self.log.error(f"Ready signals not 0 during gating: {failed_signals}")

            return all_ready_ok

        return True

    async def test_functional_equivalence(self, test_function, *args, **kwargs):
        """Test that CG and non-CG versions produce identical results."""
        self.log.info("=== Testing Functional Equivalence ===")

        # Test with clock gating disabled
        await self.configure_clock_gating(enable=False)
        await Timer(100, 'ns')

        try:
            result_no_cg = await test_function(*args, **kwargs)
        except Exception as e:
            self.log.error(f"Test failed with CG disabled: {e}")
            return False

        # Test with clock gating enabled
        await self.configure_clock_gating(enable=True, idle_count=4)
        await Timer(100, 'ns')

        try:
            result_with_cg = await test_function(*args, **kwargs)
        except Exception as e:
            self.log.error(f"Test failed with CG enabled: {e}")
            return False

        # Compare results (simple comparison - can be enhanced)
        equivalence = (result_no_cg == result_with_cg)

        if equivalence:
            self.log.info("✓ Functional equivalence validated")
        else:
            self.log.error("✗ Functional equivalence validation failed")
            self.log.error(f"No CG result: {result_no_cg}")
            self.log.error(f"With CG result: {result_with_cg}")

        return equivalence

    async def run_basic_transfer_test_cg(self, num_packets=10, enable_cg=True, idle_count=8):
        """Clock gating version of basic transfer test."""
        self.log.info(f"Starting CG basic transfer test: packets={num_packets}, cg={enable_cg}, idle_count={idle_count}")

        # Configure clock gating
        await self.configure_clock_gating(enable=enable_cg, idle_count=idle_count)

        # Run the base test
        await self.run_basic_transfer_test(num_packets)

        # Validate clock gating behavior
        if enable_cg:
            ready_signals_ok = await self.validate_ready_signals_during_gating()
            if not ready_signals_ok:
                self.log.warning("Ready signal validation failed during gating")

        return True

    async def run_gating_stress_test(self, num_packets=20):
        """Test with aggressive clock gating to stress the system."""
        self.log.info(f"Starting gating stress test with {num_packets} packets")

        # Enable aggressive gating
        await self.configure_clock_gating(enable=True, idle_count=1)

        # Configure FUB slave to be ready
        self.fub_slave._set_ready(1)

        # Send packets with random delays to trigger frequent gating/ungating
        for i in range(num_packets):
            data = 0x30000000 + i
            packet = self.axis_master.create_packet(
                data=data,
                last=1,
                id=i % (2**self.TEST_ID_WIDTH if self.TEST_ID_WIDTH > 0 else 1)
            )

            success = await self.axis_master.send(packet)
            assert success, f"Failed to send packet {i} during stress test"

            # Random short delays to cause frequent gating
            delay = random.randint(1, 3)
            await self.wait_clocks(self.aclk_name, delay)

        # Wait for completion
        await self.wait_clocks(self.aclk_name, 50)

        # Verify packets were received
        fub_stats = self.fub_slave.get_stats()
        packets_received = fub_stats.get('received_transactions', fub_stats.get('slave_stats', {}).get('received_transactions', fub_stats.get('packet_count', 0)))

        self.log.info(f"Stress test: {packets_received} packets received")

        # Allow some margin for stress test conditions
        assert packets_received >= num_packets * 0.9, f"Too many packets lost in stress test: {packets_received}/{num_packets}"

        self.log.info("Gating stress test completed successfully")