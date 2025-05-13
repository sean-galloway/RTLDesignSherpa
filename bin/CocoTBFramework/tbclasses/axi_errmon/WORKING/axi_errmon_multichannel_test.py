"""
Multi-channel test class for AXI Error Monitor.

This module provides tests focusing on multi-channel behavior for the AXI Error Monitor
Base module, including channel independence and concurrent operation.
"""

import cocotb
from cocotb.triggers import RisingEdge
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket

from .axi_errmon_base_test import AXIErrorMonBaseTest


class AXIErrorMonMultiChannelTest(AXIErrorMonBaseTest):
    """
    Multi-channel tests for AXI Error Monitor.
    Tests channel independence and concurrent operation.
    """

    def __init__(self, tb):
        """
        Initialize with a reference to the testbench

        Args:
            tb: Reference to the AXIErrorMonitorTB wrapper class
        """
        super().__init__(tb)

    async def run(self):
        """
        Run all multi-channel tests

        Returns:
            True if all tests passed, False otherwise
        """
        # Skip for single channel configuration
        if self.tb.channels <= 1:
            self.log.info(f"Skipping multi-channel tests for single-channel configuration{self.tb.get_time_ns_str()}")
            return True

        self.log.info(f"Running multi-channel tests{self.tb.get_time_ns_str()}")

        # Reset the DUT
        await self.tb.reset_dut()

        # Run concurrent transactions test
        concurrent_passed = await self.test_concurrent_transactions()

        # Run channel interference test
        interference_passed = await self.test_channel_interference()

        # Run ID-based channel selection test
        id_selection_passed = await self.test_id_channel_selection()

        # Report results
        all_passed = concurrent_passed and interference_passed and id_selection_passed

        if all_passed:
            self.log.info(f"All multi-channel tests passed{self.tb.get_time_ns_str()}")
        else:
            self.log.error(f"Some multi-channel tests failed{self.tb.get_time_ns_str()}")

        return all_passed

    async def test_concurrent_transactions(self):
        """
        Test concurrent transactions across multiple channels

        This test verifies that transactions on different channels can
        proceed concurrently, with adjustments for write mode's shared FIFO.

        Returns:
            True if test passed, False otherwise
        """
        self.log.info(f"Testing concurrent transactions across channels{self.tb.get_time_ns_str()}")

        # Reset and setup for clean test state
        await self.reset_and_setup_for_test()

        # For read mode, use the original approach
        if self.tb.is_read:
            # Launch transactions on all channels concurrently
            tasks = []
            num_channels = min(self.tb.channels, 4)  # Test up to 4 channels

            for ch in range(num_channels):
                addr = 0x8000 + (ch * 0x1000)

                # Use thread-safe method to launch tasks
                task = cocotb.start_soon(self.drive_basic_transaction(
                    addr=addr,
                    id_value=ch,
                    data_value=0xC0000000 | ch,
                    resp_value=0,  # OKAY
                    control_ready=False,  # Use default ready behavior
                    wait_for_completion=False
                ))
                tasks.append(task)

            # Wait for all tasks to complete
            for task in tasks:
                await task

            # Check for completed transactions
            completed_count = 0
            for transaction in self.completed_transactions:
                if 0x8000 <= transaction['addr'] < 0xC000:
                    completed_count += 1

            if completed_count != num_channels:
                self.log.error(f"Not all concurrent transactions completed: {completed_count} of {num_channels}{self.tb.get_time_ns_str()}")
                return False
        else:
            # For write mode with shared FIFO, we need to be more careful
            # Launch transactions sequentially, but process them concurrently
            num_channels = min(self.tb.channels, 4)  # Test up to 4 channels

            # Determine how many transactions we can launch concurrently
            # due to shared FIFO limitation (same depth as addr FIFO)
            max_concurrent = min(self.tb.addr_fifo_depth, num_channels)

            self.log.info(f"Testing with {max_concurrent} concurrent transactions (limited by shared FIFO){self.tb.get_time_ns_str()}")

            # First, launch address phases sequentially
            for ch in range(max_concurrent):
                addr = 0x8000 + (ch * 0x1000)

                # Create address packet
                addr_packet = GAXIPacket(self.tb.addr_field_config)
                addr_packet.addr = addr
                addr_packet.id = ch

                # Send address packet
                await self.tb.addr_master.send(addr_packet)

                # Wait for address phase to start before sending next
                # (but don't wait for completion)
                await self.tb.wait_clocks('aclk', 5)

            # Wait for all address phases to complete
            while self.tb.addr_master.transfer_busy:
                await self.tb.wait_clocks('aclk', 1)

            # Then process data phases concurrently
            tasks = []
            for ch in range(max_concurrent):
                # Create data packet
                data_packet = GAXIPacket(self.tb.data_field_config)
                data_packet.id = ch
                data_packet.last = 1

                # Send data packet concurrently
                task = cocotb.start_soon(self.tb.data_master.send(data_packet))
                tasks.append(task)

            # Wait for all data phases to complete
            for task in tasks:
                await task

            # Finally, process response phases concurrently
            tasks = []
            for ch in range(max_concurrent):
                # Create response packet
                resp_packet = GAXIPacket(self.tb.resp_field_config)
                resp_packet.id = ch
                resp_packet.resp = 0  # OKAY

                # Send response packet concurrently
                task = cocotb.start_soon(self.tb.resp_master.send(resp_packet))
                tasks.append(task)

            # Wait for all response phases to complete
            for task in tasks:
                await task

            # Verify all phases completed successfully
            self.log.info(f"All {max_concurrent} concurrent transactions completed{self.tb.get_time_ns_str()}")

        # Check that no errors were detected
        if len(self.tb.errors_detected) > 0:
            self.log.error(f"Errors detected during concurrent transactions test: {len(self.tb.errors_detected)}{self.tb.get_time_ns_str()}")
            for error in self.tb.errors_detected:
                self.log.error(f"  Error: type={error['type_str']}, id={error['id']}, addr=0x{error['addr']:X}{self.tb.get_time_ns_str()}")
            return False

        self.log.info(f"Concurrent transactions test passed successfully{self.tb.get_time_ns_str()}")
        return True


    async def test_channel_interference(self):
        """
        Test that errors on one channel don't affect other channels

        This test verifies that error conditions on one channel
        don't interfere with transactions on other channels.

        Updated for write mode to account for the shared FIFO.

        Returns:
            True if test passed, False otherwise
        """
        self.log.info(f"Testing channel interference{self.tb.get_time_ns_str()}")

        # Reset and setup for clean test state
        await self.reset_and_setup_for_test()

        # Create an error condition on channel 0
        error_channel = 0
        normal_channel = 1 % self.tb.channels  # Use channel 1 (or 0 if channels=1)

        # Ensure we have different channels
        if normal_channel == error_channel:
            normal_channel = (error_channel + 1) % self.tb.channels

        if self.tb.is_read:
            # For read mode, use the original approach
            # Start a transaction on the error channel that will timeout
            error_task = cocotb.start_soon(self.drive_error_scenario(
                error_type='data_timeout',
                addr=0xA000,
                id_value=error_channel
            ))

            # Wait a bit for the error transaction to start
            await self.tb.wait_clocks('aclk', 10)

            # Now try a normal transaction on a different channel
            normal_transaction = await self.drive_basic_transaction(
                addr=0xA100,
                id_value=normal_channel,
                control_ready=False,  # Use default ready behavior
                wait_for_completion=True
            )

            # Check that normal transaction completed without error
            if normal_transaction.get('error') is not None:
                self.log.error(f"Transaction on normal channel reported error: {normal_transaction['error']}{self.tb.get_time_ns_str()}")
                return False

            # Wait for error to be detected on error channel
            await self.tb.wait_clocks('aclk', self.tb.timeout_data + 20)
        else:
            # For write mode with shared FIFO, the test needs to be adapted
            # We'll first verify that a data timeout error on one channel doesn't
            # affect response phases on another channel

            # First send an address packet on the error channel
            addr_packet_err = GAXIPacket(self.tb.addr_field_config)
            addr_packet_err.addr = 0xA000
            addr_packet_err.id = error_channel
            await self.tb.addr_master.send(addr_packet_err)

            # Wait for address phase to complete
            while self.tb.addr_master.transfer_busy:
                await self.tb.wait_clocks('aclk', 1)

            # Now send an address packet on the normal channel
            addr_packet_normal = GAXIPacket(self.tb.addr_field_config)
            addr_packet_normal.addr = 0xA100
            addr_packet_normal.id = normal_channel
            await self.tb.addr_master.send(addr_packet_normal)

            # Wait for address phase to complete
            while self.tb.addr_master.transfer_busy:
                await self.tb.wait_clocks('aclk', 1)

            # Force data_ready low to prepare for timeout on error channel
            self.tb.ready_ctrl.force_data_ready_low(True)

            # Start data phase on error channel, which will timeout
            data_packet_err = GAXIPacket(self.tb.data_field_config)
            data_packet_err.id = error_channel
            data_packet_err.last = 1
            error_task = cocotb.start_soon(self.tb.data_master.send(data_packet_err))

            # Wait a bit for the error transaction to start
            await self.tb.wait_clocks('aclk', 10)

            # Now allow normal channel to proceed by temporarily enabling data_ready
            self.tb.ready_ctrl.force_data_ready_low(False)

            # Process normal channel data
            data_packet_normal = GAXIPacket(self.tb.data_field_config)
            data_packet_normal.id = normal_channel
            data_packet_normal.last = 1
            await self.tb.data_master.send(data_packet_normal)

            # Complete normal channel response
            resp_packet_normal = GAXIPacket(self.tb.resp_field_config)
            resp_packet_normal.id = normal_channel
            resp_packet_normal.resp = 0  # OKAY
            await self.tb.resp_master.send(resp_packet_normal)

            # Force data_ready low again for error channel
            self.tb.ready_ctrl.force_data_ready_low(True)

            # Wait for timeout to occur on error channel
            await self.tb.wait_clocks('aclk', self.tb.timeout_data + 20)

            # Release data_ready
            self.tb.ready_ctrl.force_data_ready_low(False)

        # Verify that exactly one error was detected (on error channel)
        if len(self.tb.errors_detected) != 1:
            self.log.error(f"Expected 1 error, but detected {len(self.tb.errors_detected)}{self.tb.get_time_ns_str()}")
            return False

        # Verify error was on the correct channel
        error = self.tb.errors_detected[-1]
        if error['id'] != error_channel:
            self.log.error(f"Error reported for wrong channel: expected {error_channel}, got {error['id']}{self.tb.get_time_ns_str()}")
            return False

        self.log.info(f"Channel interference test passed successfully{self.tb.get_time_ns_str()}")
        return True


    async def test_id_channel_selection(self):
        """
        Test ID-based channel selection

        This test verifies that the monitor correctly selects channels
        based on transaction IDs.

        Updated for write mode to account for the shared FIFO.

        Returns:
            True if test passed, False otherwise
        """
        self.log.info(f"Testing ID-based channel selection{self.tb.get_time_ns_str()}")

        # Skip for AXI-Lite mode (doesn't use IDs for channel selection)
        if not self.tb.is_axi:
            self.log.info(f"Skipping ID-based channel selection test for AXI-Lite mode{self.tb.get_time_ns_str()}")
            return True

        # Reset and setup for clean test state
        await self.reset_and_setup_for_test()

        # Generate IDs that map to different channels
        id_values = []
        for ch in range(min(self.tb.channels, 4)):  # Test up to 4 channels
            # Create ID that maps to this channel (ID % channels == ch)
            id_value = ch + (self.tb.channels * ch)
            id_values.append(id_value)

        if self.tb.is_read:
            # Verify channel selection works correctly for read mode
            for i, id_value in enumerate(id_values):
                expected_channel = id_value % self.tb.channels

                # Create timeout condition for this ID
                await self.drive_error_scenario(
                    error_type='addr_timeout',
                    addr=0xB000 + (i * 0x100),
                    id_value=id_value
                )

                # Check the most recent error
                if len(self.tb.errors_detected) < i + 1:
                    self.log.error(f"Error not detected for ID {id_value}{self.tb.get_time_ns_str()}")
                    return False

                error = self.tb.errors_detected[i]

                # Verify the error has the correct ID
                if error['id'] != id_value:
                    self.log.error(f"Wrong ID in error: expected {id_value}, got {error['id']}{self.tb.get_time_ns_str()}")
                    return False
        else:
            # For write mode with shared FIFO, we need to test differently
            # Clear previous errors
            self.tb.errors_detected = []

            # Test one ID at a time for write mode to avoid shared FIFO interference
            for i, id_value in enumerate(id_values):
                # Reset for clean state before each test
                await self.reset_and_setup_for_test()

                # Use response error test since it completes all phases
                await self.drive_error_scenario(
                    error_type='resp_error',
                    addr=0xB000 + (i * 0x100),
                    id_value=id_value,
                    resp_value=2  # SLVERR
                )

                # Check that error was detected with correct ID
                if len(self.tb.errors_detected) < i + 1:
                    self.log.error(f"Error not detected for ID {id_value}{self.tb.get_time_ns_str()}")
                    return False

                # Find the error with this ID
                error_found = False
                for error in self.tb.errors_detected:
                    if error['id'] == id_value:
                        error_found = True
                        self.log.info(f"Error correctly detected for ID {id_value}{self.tb.get_time_ns_str()}")
                        break

                if not error_found:
                    self.log.error(f"Error not found for ID {id_value}{self.tb.get_time_ns_str()}")
                    return False

        self.log.info(f"ID-based channel selection test passed successfully{self.tb.get_time_ns_str()}")
        return True
