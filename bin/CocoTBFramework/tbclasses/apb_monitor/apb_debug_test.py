# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBDebugTest
# Purpose: APB Monitor Debug Event Test - FIXED VERSION
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
APB Monitor Debug Event Test - FIXED VERSION

Tests that the APB monitor generates debug events for transaction state changes.
This test focuses ONLY on debug events - all other monitor features are disabled.

CHANGES:
- Uses MonbusPktType instead of APBMonitorEventType
- Uses integer packet type comparisons
- Consistent imports from monbus_components
"""

import cocotb
from cocotb.triggers import Timer

from .apb_monitor_core_tb import (
    APBMonitorCoreTB, APBMonitorConfiguration, ReadySignalPattern
)
# FIXED: Use consistent imports from monbus_components
from CocoTBFramework.tbclasses.misc.monbus_components import (
    MonbusPktType, APBDebugCode
)
from .apb_monitor_packets import APBMonitorEvent


class APBDebugTest(APBMonitorCoreTB):
    """Test class focused on APB debug events"""

    def get_test_configuration(self) -> APBMonitorConfiguration:
        """Return configuration that enables ONLY debug event generation"""
        config = APBMonitorConfiguration()

        # Disable error and performance features
        config.error_enable = False
        config.timeout_enable = False
        config.protocol_enable = False
        config.slverr_enable = False
        config.perf_enable = False
        config.latency_enable = False
        config.throughput_enable = False

        # Enable debug features
        config.debug_enable = True
        config.trans_debug_enable = True
        config.debug_level = 0xF  # Maximum debug level

        return config

    async def run_debug_test(self) -> bool:
        """Run the debug event test"""
        self.log.info("🧪 Testing APB Debug Events")

        # Setup with debug-focused configuration
        monitor_config = self.get_test_configuration()
        ready_config = ReadySignalPattern.immediate()

        await self.setup_clocks_and_reset(monitor_config, ready_config)

        # FIXED: Use MonbusPktType and integer packet type
        expected_event = APBMonitorEvent(
            packet_type=MonbusPktType.DEBUG.value,  # ✅ Integer-based packet type
            event_code=APBDebugCode.SETUP_PHASE.value,
            tolerance_ns=1000.0
        )
        self.scoreboard.expect_monitor_event(expected_event)

        # Send a single transaction that should generate debug events
        addr = 0x3000
        data = 0x12345678

        self.log.info(f"Sending transaction for debug monitoring: addr=0x{addr:08X}, data=0x{data:08X}")
        txn_id = await self.send_write_transaction(addr, data, expect_error=False)

        # Wait for monitor to process the transaction
        await self.wait_for_monitor_packets(expected_count=1, timeout_cycles=50)

        # Additional wait to ensure all processing is complete
        await Timer(100, units='ns')

        # FIXED: Use integer-based packet type comparison
        debug_packets = self.monbus_slave.get_debug_packets()
        total_packets = self.test_stats['monitor_packets_received']

        self.log.info(f"Results: {total_packets} total packets, {len(debug_packets)} debug packets")

        # Check if we got the expected debug event
        if len(debug_packets) >= 1:
            # Verify it's the right type of debug event
            debug_pkt = debug_packets[0]
            if debug_pkt.event_code == APBDebugCode.SETUP_PHASE.value:
                self.log.info("✅ SETUP_PHASE debug event detected successfully")

                # Log additional details about the debug packet
                self.log.info(f"Debug packet details:")
                self.log.info(f"  Event code: 0x{debug_pkt.event_code:X} ({APBDebugCode.SETUP_PHASE.name})")
                self.log.info(f"  Data: 0x{debug_pkt.data:X}")
                self.log.info(f"  Unit ID: 0x{debug_pkt.unit_id:X}")
                self.log.info(f"  Agent ID: 0x{debug_pkt.agent_id:X}")

                return True
            else:
                self.log.warning(f"⚠️ Got debug event but wrong code: 0x{debug_pkt.event_code:X} (expected 0x{APBDebugCode.SETUP_PHASE.value:X})")
                return False
        elif total_packets > 0:
            # We got some packets but not debug - log what we got
            all_packets = self.monbus_slave.get_received_packets()
            for i, pkt in enumerate(all_packets):
                self.log.info(f"  Packet {i}: {pkt.get_packet_type_name()}.{pkt.get_event_code_name()}")

            self.log.warning(f"⚠️ Got {total_packets} monitor packets but no debug events")
            return False
        else:
            self.log.error("❌ No monitor packets received - check RTL configuration")
            return False

    async def verify_debug_behavior(self) -> bool:
        """Verify that debug events match expected behavior"""
        # Run the scoreboard verification
        verification_passed = self.scoreboard.verify_monitor_behavior()

        if verification_passed:
            self.log.info("✅ Debug event verification PASSED")
        else:
            self.log.error("❌ Debug event verification FAILED")

        return verification_passed


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def test_apb_debug_events(dut):
    """CocoTB test entry point for APB debug events"""

    test = APBDebugTest(dut)

    try:
        # Run the debug-specific test
        test_passed = await test.run_debug_test()

        # Verify the behavior
        verification_passed = await test.verify_debug_behavior()

        # Overall result
        overall_passed = test_passed and verification_passed

        # Shutdown
        await test.shutdown()

        # Final result
        if overall_passed:
            test.log.info("🎉 APB Debug Event Test PASSED")
        else:
            test.log.error("💥 APB Debug Event Test FAILED")

        assert overall_passed, "APB debug event test failed"

    except Exception as e:
        test.log.error(f"Test failed with exception: {e}")
        await test.shutdown()
        raise
