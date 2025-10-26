# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBErrorTest
# Purpose: APB Monitor Error Event Test - FIXED VERSION
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
APB Monitor Error Event Test - FIXED VERSION

Tests that the APB monitor generates error events for failed transactions.
This test focuses ONLY on error events - all other monitor features are disabled.

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
    MonbusPktType, APBErrorCode
)
from .apb_monitor_packets import APBMonitorEvent


class APBErrorTest(APBMonitorCoreTB):
    """Test class focused on APB error events"""

    def get_test_configuration(self) -> APBMonitorConfiguration:
        """Return configuration that enables ONLY error event generation"""
        config = APBMonitorConfiguration()
        
        # Enable error detection features
        config.error_enable = True
        config.protocol_enable = True
        config.slverr_enable = True
        config.timeout_enable = False  # We'll test timeouts separately
        
        # Disable performance and debug features
        config.perf_enable = False
        config.latency_enable = False
        config.throughput_enable = False
        config.debug_enable = False
        config.trans_debug_enable = False
        config.debug_level = 0x0
        
        return config

    async def run_error_test(self) -> bool:
        """Run the error event test"""
        self.log.info("🧪 Testing APB Error Events")
        
        # Setup with error-focused configuration
        monitor_config = self.get_test_configuration()
        ready_config = ReadySignalPattern.immediate()
        
        await self.setup_clocks_and_reset(monitor_config, ready_config)
        
        # FIXED: Use MonbusPktType and integer packet type
        expected_event = APBMonitorEvent(
            packet_type=MonbusPktType.ERROR.value,  # ✅ Integer-based packet type
            event_code=APBErrorCode.PSLVERR.value,
            expected_data=0x2000,  # Expected address where error occurs
            tolerance_ns=1000.0
        )
        self.scoreboard.expect_monitor_event(expected_event)
        
        # Send a single transaction that should generate a PSLVERR
        addr = 0x2000
        data = 0xBADCAFE
        
        self.log.info(f"Sending error-inducing transaction: addr=0x{addr:08X}, data=0x{data:08X}")
        txn_id = await self.send_write_transaction(addr, data, expect_error=True)
        
        # Wait for monitor to process the transaction
        await self.wait_for_monitor_packets(expected_count=1, timeout_cycles=50)
        
        # Additional wait to ensure all processing is complete
        await Timer(100, units='ns')
        
        # FIXED: Use integer-based packet type comparison
        error_packets = self.monbus_slave.get_error_packets()
        total_packets = self.test_stats['monitor_packets_received']
        
        self.log.info(f"Results: {total_packets} total packets, {len(error_packets)} error packets")
        
        # Check if we got the expected error event
        if len(error_packets) >= 1:
            # Verify it's the right type of error
            error_pkt = error_packets[0]
            if error_pkt.event_code == APBErrorCode.PSLVERR.value:
                self.log.info("✅ PSLVERR error event detected successfully")
                
                # Log additional details about the error packet
                self.log.info(f"Error packet details:")
                self.log.info(f"  Event code: 0x{error_pkt.event_code:X} ({APBErrorCode.PSLVERR.name})")
                self.log.info(f"  Data: 0x{error_pkt.data:X}")
                self.log.info(f"  Unit ID: 0x{error_pkt.unit_id:X}")
                self.log.info(f"  Agent ID: 0x{error_pkt.agent_id:X}")
                
                return True
            else:
                self.log.warning(f"⚠️ Got error event but wrong code: {error_pkt.event_code} (expected {APBErrorCode.PSLVERR.value})")
                return False
        elif total_packets > 0:
            # We got some packets but not error - log what we got
            all_packets = self.monbus_slave.get_received_packets()
            for i, pkt in enumerate(all_packets):
                self.log.info(f"  Packet {i}: {pkt.get_packet_type_name()}.{pkt.get_event_code_name()}")
            
            self.log.warning(f"⚠️ Got {total_packets} monitor packets but no error events")
            return False
        else:
            self.log.error("❌ No monitor packets received - check RTL configuration")
            return False

    async def verify_error_behavior(self) -> bool:
        """Verify that error events match expected behavior"""
        # Run the scoreboard verification
        verification_passed = self.scoreboard.verify_monitor_behavior()
        
        if verification_passed:
            self.log.info("✅ Error event verification PASSED")
        else:
            self.log.error("❌ Error event verification FAILED")
            
        return verification_passed


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def test_apb_error_events(dut):
    """CocoTB test entry point for APB error events"""
    
    test = APBErrorTest(dut)
    
    try:
        # Run the error-specific test
        test_passed = await test.run_error_test()
        
        # Verify the behavior
        verification_passed = await test.verify_error_behavior()
        
        # Overall result
        overall_passed = test_passed and verification_passed
        
        # Shutdown
        await test.shutdown()
        
        # Final result
        if overall_passed:
            test.log.info("🎉 APB Error Event Test PASSED")
        else:
            test.log.error("💥 APB Error Event Test FAILED")
            
        assert overall_passed, "APB error event test failed"
        
    except Exception as e:
        test.log.error(f"Test failed with exception: {e}")
        await test.shutdown()
        raise
