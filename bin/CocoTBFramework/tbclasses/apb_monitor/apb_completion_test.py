# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBCompletionTest
# Purpose: APB Monitor Completion Event Test - FIXED VERSION
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
APB Monitor Completion Event Test - FIXED VERSION

Tests that the APB monitor generates completion events for successful transactions.
This test focuses ONLY on completion events - all other monitor features are disabled.

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
    MonbusPktType, APBCompletionCode
)
from .apb_monitor_packets import APBMonitorEvent


class APBCompletionTest(APBMonitorCoreTB):
    """Test class focused on APB completion events"""

    def get_test_configuration(self) -> APBMonitorConfiguration:
        """Return configuration that enables ONLY completion event generation"""
        config = APBMonitorConfiguration()
        
        # Disable everything except what's needed for completion events
        config.error_enable = False
        config.timeout_enable = False
        config.protocol_enable = False
        config.slverr_enable = False
        config.perf_enable = False
        config.latency_enable = False
        config.throughput_enable = False
        config.debug_enable = False
        config.trans_debug_enable = False
        config.debug_level = 0x0
        
        # Enable only what's necessary for completion detection
        # (This might need adjustment based on your RTL implementation)
        # Some monitors require error detection to be enabled to generate completion events
        config.error_enable = True  # May be needed for completion event generation
        config.slverr_enable = True  # Needed to distinguish error vs completion
        
        return config

    async def run_completion_test(self) -> bool:
        """Run the completion event test"""
        self.log.info("🧪 Testing APB Completion Events")
        
        # Setup with completion-focused configuration
        monitor_config = self.get_test_configuration()
        ready_config = ReadySignalPattern.immediate()
        
        await self.setup_clocks_and_reset(monitor_config, ready_config)
        
        # FIXED: Use MonbusPktType and integer packet type
        expected_event = APBMonitorEvent(
            packet_type=MonbusPktType.COMPLETION.value,  # ✅ Integer-based packet type
            event_code=APBCompletionCode.TRANS_COMPLETE.value,
            tolerance_ns=1000.0
        )
        self.scoreboard.expect_monitor_event(expected_event)
        
        # Send a single successful write transaction
        addr = 0x1000
        data = 0xDEADBEEF
        
        self.log.info(f"Sending write transaction: addr=0x{addr:08X}, data=0x{data:08X}")
        txn_id = await self.send_write_transaction(addr, data, expect_error=False)
        
        # Wait for monitor to process the transaction
        await self.wait_for_monitor_packets(expected_count=1, timeout_cycles=50)
        
        # Additional wait to ensure all processing is complete
        await Timer(100, units='ns')
        
        # FIXED: Use integer-based packet type comparison
        completion_packets = self.monbus_slave.get_completion_packets()
        total_packets = self.test_stats['monitor_packets_received']
        
        self.log.info(f"Results: {total_packets} total packets, {len(completion_packets)} completion packets")
        
        # Check if we got the expected completion event
        if len(completion_packets) >= 1:
            self.log.info("✅ Completion event detected successfully")
            
            # Log details about the completion packet
            completion_pkt = completion_packets[0]
            self.log.info(f"Completion packet details:")
            self.log.info(f"  Event code: 0x{completion_pkt.event_code:X}")
            self.log.info(f"  Data: 0x{completion_pkt.data:X}")
            self.log.info(f"  Unit ID: 0x{completion_pkt.unit_id:X}")
            self.log.info(f"  Agent ID: 0x{completion_pkt.agent_id:X}")
            
            return True
        elif total_packets > 0:
            # We got some packets but not completion - log what we got
            all_packets = self.monbus_slave.get_received_packets()
            for i, pkt in enumerate(all_packets):
                self.log.info(f"  Packet {i}: {pkt.get_packet_type_name()}.{pkt.get_event_code_name()}")
            
            self.log.warning(f"⚠️ Got {total_packets} monitor packets but no completion events")
            return False
        else:
            self.log.error("❌ No monitor packets received - check RTL configuration")
            return False

    async def verify_completion_behavior(self) -> bool:
        """Verify that completion events match expected behavior"""
        # Run the scoreboard verification
        verification_passed = self.scoreboard.verify_monitor_behavior()
        
        if verification_passed:
            self.log.info("✅ Completion event verification PASSED")
        else:
            self.log.error("❌ Completion event verification FAILED")
            
        return verification_passed
