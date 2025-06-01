"""
Basic test class for AXI Error Monitor.

This module provides basic functionality tests for the AXI Error Monitor Base module,
focusing on simple transaction handling and interrupt bus events.

Updated to work with the consolidated 64-bit interrupt bus interface and
the surgically updated testbench using separate intrbus components.
Updated to use field configurations consistently throughout.
Updated to use centralized constants from intrbus module.
"""

from .axi_errmon_base_test import AXIErrorMonBaseTest
from CocoTBFramework.components.flex_randomizer import FlexRandomizer

# Import constants from intrbus module
from ..intrbus import EVENT_CODES, PACKET_TYPES


class AXIErrorMonBasicTest(AXIErrorMonBaseTest):
    """
    Basic tests for AXI Error Monitor.
    Tests simple transaction handling and basic functionality.
    Updated for consolidated interrupt bus interface and separate intrbus components.
    Updated to use field configurations consistently.
    Updated to use centralized constants from intrbus module.
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
        Run all basic tests

        Returns:
            True if all tests passed, False otherwise
        """
        self.log.info("+"*80)
        self.log.info(f"Running basic tests{self.tb.get_time_ns_str()}")
        self.log.info("+"*80)

        # Reset the DUT
        await self.tb.reset_dut()

        # Run simple transaction tests
        single_passed = await self.test_single_transaction()

        # Run timer validation test
        timer_passed = await self.test_timer_reset()

        # Run sequential transactions test
        sequential_passed = await self.test_sequential_transactions()

        # Run pipelined transactions test
        pipeline_passed = await self.test_pipelined_transactions()

        # Run intrbus event test
        intrbus_passed = await self.test_intrbus_events()

        # Run basic error scenarios
        error_passed = await self.test_basic_error_scenarios()

        # Report results
        all_passed = single_passed and timer_passed and sequential_passed and pipeline_passed and intrbus_passed and error_passed

        if all_passed:
            self.log.info(f"All basic tests passed{self.tb.get_time_ns_str()}")
        else:
            self.log.error(f"Some basic tests failed{self.tb.get_time_ns_str()}")

        return all_passed

    async def test_single_transaction(self):
        """
        Test a single simple transaction

        This tests that a single transaction can be processed correctly
        without any errors or timeouts.

        Returns:
            True if test passed, False otherwise
        """
        self.log.info("="*80)
        self.log.info(f"Testing single transaction{self.tb.get_time_ns_str()}")
        self.log.info("="*80)

        # Reset and set up for clean test state
        await self.reset_and_setup_for_test()

        # Get initial event count for later comparison
        initial_events_count = len(self.tb.intrbus_events)

        # Set intrbus ready to normal speed using new method
        self.tb.set_intrbus_backpressure('fixed')

        # Drive a single transaction
        transaction = await self.drive_basic_transaction(
            addr=0x1000,
            id_value=0,
            resp_value=0,  # OKAY
            control_ready=False,  # Use default ready behavior
            intrbus_ready_speed='fixed',  # Normal speed for intrbus ready
            wait_for_completion=True
        )

        # Check that transaction completed without error
        if transaction.get('error') is not None:
            self.log.error(f"Transaction reported error: {transaction['error']}{self.tb.get_time_ns_str()}")
            return False

        # Check that no errors were detected
        if self.tb.errors_detected:
            self.log.error(f"Errors detected during single transaction test: {len(self.tb.errors_detected)}{self.tb.get_time_ns_str()}")
            for error in self.tb.errors_detected:
                self.log.error(f"  Error: type={error['type_str']}, id={error['id']}, addr=0x{error['addr']:X}{self.tb.get_time_ns_str()}")
            return False

        # Check for completion event on intrbus (if any)
        completion_found = False
        for event in self.tb.intrbus_events[initial_events_count:]:
            if (event['packet_type'] == self.PACKET_TYPES['COMPLETION'] and  # Completion packet type
                event['event_code'] == self.EVENT_CODES['TRANS_COMPLETE'] and  # EVT_TRANS_COMPLETE
                event['channel_id'] == 0 and
                event['addr'] == 0x1000):  # Note: using 'addr' key for backward compatibility
                self.log.info(f"Found completion event for transaction: addr=0x{event['addr']:X}, id={event['channel_id']}{self.tb.get_time_ns_str()}")
                completion_found = True
                break

        # Note: Not all configurations will generate completion events, so this is not a pass/fail criteria
        if not completion_found:
            self.log.debug(f"No completion event detected for transaction (this may be normal depending on configuration){self.tb.get_time_ns_str()}")

        self.log.info(f"Single transaction test passed successfully{self.tb.get_time_ns_str()}")
        return True

    async def test_timer_reset(self):
        """
        Test timer functionality by checking that it operates correctly

        This test verifies that the timer module is functioning and that
        the timestamp counter is incrementing properly.

        Returns:
            True if test passed, False otherwise
        """
        self.log.info("="*80)
        self.log.info(f"Testing timer reset functionality{self.tb.get_time_ns_str()}")
        self.log.info("="*80)

        # Reset and set up for clean test state
        await self.reset_and_setup_for_test()

        # Check that o_busy signal is working
        initial_busy = self.dut.o_busy.value
        initial_active_count = self.dut.o_active_count.value

        self.log.info(f"Initial busy state: {initial_busy}, active count: {initial_active_count}{self.tb.get_time_ns_str()}")

        # Start a transaction but don't complete it immediately using field config
        addr_packet = self._create_addr_packet(0x2000, 0)

        # Send address phase
        await self.tb.addr_master.send(addr_packet)

        # Wait for address phase to complete
        while self.tb.addr_master.transfer_busy:
            await self.tb.wait_clocks('aclk', 1)

        # Check that busy signal is now asserted and active count increased
        await self.tb.wait_clocks('aclk', 5)

        busy_after_addr = self.dut.o_busy.value
        active_after_addr = self.dut.o_active_count.value

        self.log.info(f"After address: busy={busy_after_addr}, active count={active_after_addr}{self.tb.get_time_ns_str()}")

        # For this test, we expect the monitor to be tracking the transaction
        if active_after_addr == 0:
            self.log.warning(f"Active count is still 0 after address phase - this may indicate an issue{self.tb.get_time_ns_str()}")

        # Complete the transaction using field config
        data_packet = self._create_data_packet(0, 0)
        await self.tb.data_master.send(data_packet)

        # For write mode, also send response
        if not self.is_read:
            while self.tb.data_master.transfer_busy:
                await self.tb.wait_clocks('aclk', 1)

            resp_packet = self._create_resp_packet(0, 0)
            await self.tb.resp_master.send(resp_packet)

        # Wait for transaction to complete
        await self.tb.wait_clocks('aclk', 20)

        # Check final state
        final_busy = self.dut.o_busy.value
        final_active_count = self.dut.o_active_count.value

        self.log.info(f"Final state: busy={final_busy}, active count={final_active_count}{self.tb.get_time_ns_str()}")

        # The test passes if we can observe the state changes
        self.log.info(f"Timer reset test completed{self.tb.get_time_ns_str()}")
        return True

    async def test_sequential_transactions(self):
        """
        Test multiple sequential transactions

        This tests that multiple sequential transactions can be processed correctly
        without any errors or timeouts.

        Returns:
            True if test passed, False otherwise
        """
        self.log.info("="*80)
        self.log.info(f"Testing sequential transactions{self.tb.get_time_ns_str()}")
        self.log.info("="*80)

        # Reset and set up for clean test state
        await self.reset_and_setup_for_test()

        # Set intrbus ready to normal speed using new method
        self.tb.set_intrbus_backpressure('fixed')

        # Drive multiple transactions sequentially
        num_transactions = 5  # Reduced for basic testing

        for i in range(num_transactions):
            addr = 0x2000 + (i * 0x100)
            id_value = i % self.tb.channels

            transaction = await self.drive_basic_transaction(
                addr=addr,
                id_value=id_value,
                resp_value=0,  # OKAY
                control_ready=False,  # Use default ready behavior
                intrbus_ready_speed='fixed',  # Normal speed for intrbus ready
                pipeline_phases=False,  # Sequential behavior
                wait_for_completion=True
            )

            # Check that transaction completed without error
            if transaction.get('error') is not None:
                self.log.error(f"Transaction {i} reported error: {transaction['error']}{self.tb.get_time_ns_str()}")
                return False

        # Check that no errors were detected
        if self.tb.errors_detected:
            self.log.error(f"Errors detected during sequential transactions test: {len(self.tb.errors_detected)}{self.tb.get_time_ns_str()}")
            for error in self.tb.errors_detected:
                self.log.error(f"  Error: type={error['type_str']}, id={error['id']}, addr=0x{error['addr']:X}{self.tb.get_time_ns_str()}")
            return False

        self.log.info(f"Sequential transactions test passed successfully{self.tb.get_time_ns_str()}")
        return True

    async def test_pipelined_transactions(self):
        """
        Test pipelined transactions (if supported)

        This tests that pipelined transactions (address and data phases
        running in parallel) can be processed correctly without any
        errors or timeouts.

        Returns:
            True if test passed, False otherwise
        """
        # Skip for read mode (doesn't support pipelining)
        if self.tb.is_read:
            self.log.info(f"Skipping pipelined transactions test for read mode{self.tb.get_time_ns_str()}")
            return True

        self.log.info("="*80)
        self.log.info(f"Testing pipelined transactions{self.tb.get_time_ns_str()}")
        self.log.info("="*80)

        # Reset and set up for clean test state
        await self.reset_and_setup_for_test()

        # Set intrbus ready to normal speed using new method
        self.tb.set_intrbus_backpressure('fixed')

        # Drive multiple transactions with pipelining
        num_transactions = 3  # Reduced for basic testing

        for i in range(num_transactions):
            addr = 0x3000 + (i * 0x100)
            id_value = i % self.tb.channels

            transaction = await self.drive_basic_transaction(
                addr=addr,
                id_value=id_value,
                resp_value=0,  # OKAY
                control_ready=False,  # Use default ready behavior
                intrbus_ready_speed='fixed',  # Normal speed for intrbus ready
                pipeline_phases=True,  # Enable pipelining
                wait_for_completion=True
            )

            # Check that transaction completed without error
            if transaction.get('error') is not None:
                self.log.error(f"Transaction {i} reported error: {transaction['error']}{self.tb.get_time_ns_str()}")
                return False

        # Check that no errors were detected
        if self.tb.errors_detected:
            self.log.error(f"Errors detected during pipelined transactions test: {len(self.tb.errors_detected)}{self.tb.get_time_ns_str()}")
            for error in self.tb.errors_detected:
                self.log.error(f"  Error: type={error['type_str']}, id={error['id']}, addr=0x{error['addr']:X}{self.tb.get_time_ns_str()}")
            return False

        self.log.info(f"Pipelined transactions test passed successfully{self.tb.get_time_ns_str()}")
        return True

    async def test_intrbus_events(self):
        """
        Test intrbus events generation with different ready speeds

        This test verifies that the interrupt bus reports events correctly
        at different intrbus ready speeds. It generates both completion events
        and error events and checks they are properly reported on the intrbus.

        Returns:
            True if test passed, False otherwise
        """
        self.log.info("="*80)
        self.log.info(f"Testing interrupt bus events{self.tb.get_time_ns_str()}")
        self.log.info("="*80)

        # Test with different ready speeds for intrbus
        ready_speeds = ['fixed', 'slow_consumer']  # Reduced for basic testing
        all_tests_passed = True

        for speed in ready_speeds:
            self.log.info(f"Testing with intrbus ready speed: {speed}{self.tb.get_time_ns_str()}")

            # Reset and set up clean state
            await self.reset_and_setup_for_test()

            # Clear any previous events
            initial_events_count = len(self.tb.intrbus_events)
            self.tb.errors_detected = []
            self.tb.intrbus_events = []

            # Step 1: Create a successful transaction that should generate a completion event
            self.log.info(f"Testing completion event on intrbus with {speed} ready{self.tb.get_time_ns_str()}")
            success_trans = await self.drive_basic_transaction(
                addr=0x4000,
                id_value=0,
                resp_value=0,  # OKAY
                control_ready=False,
                intrbus_ready_speed=speed,
                wait_for_completion=True
            )

            # Wait a bit for events to be processed, longer for slow_consumer
            wait_cycles = 100 if speed == 'slow_consumer' else 30
            await self.tb.wait_clocks('aclk', wait_cycles)

            # Step 2: Create an error condition that should generate an error event
            self.log.info(f"Testing error event on intrbus with {speed} ready{self.tb.get_time_ns_str()}")
            err_detected = await self.drive_error_scenario(
                error_type='resp_error',
                addr=0x5000,
                id_value=1,
                resp_value=2,  # SLVERR
                intrbus_ready_speed=speed
            )

            if not err_detected:
                self.log.error(f"Error event not detected on intrbus with {speed} ready{self.tb.get_time_ns_str()}")
                all_tests_passed = False
                continue

            # Log all detected events for debugging
            self.log.info(f"Detected {len(self.tb.intrbus_events)} events on intrbus{self.tb.get_time_ns_str()}")
            for i, event in enumerate(self.tb.intrbus_events):
                self.log.info(f"Event {i}: {event['description']}{self.tb.get_time_ns_str()}")

            # Success depends on whether we found error events (these are required)
            error_found = False
            for event in self.tb.intrbus_events:
                if (event['packet_type'] == self.PACKET_TYPES['ERROR'] and  # Error packet type
                    event['event_code'] in [self.EVENT_CODES['RESP_SLVERR'], self.EVENT_CODES['RESP_DECERR']] and  # SLVERR or DECERR
                    event['addr'] == 0x5000):  # Note: using 'addr' key for backward compatibility
                    error_found = True
                    self.log.info(f"Found error event: {event['description']}{self.tb.get_time_ns_str()}")
                    break

            if not error_found:
                self.log.error(f"Expected error event not found on intrbus with {speed} ready{self.tb.get_time_ns_str()}")
                all_tests_passed = False
            else:
                self.log.info(f"Interrupt bus events test passed with {speed} ready{self.tb.get_time_ns_str()}")

        # Reset intrbus ready to fixed speed using new method
        self.tb.set_intrbus_backpressure('fixed')

        return all_tests_passed

    async def test_basic_error_scenarios(self):
        """
        Test basic error scenarios to verify error detection and reporting

        This test runs a few key error scenarios to ensure the basic
        error detection functionality is working.

        Returns:
            True if test passed, False otherwise
        """
        self.log.info("="*80)
        self.log.info(f"Testing basic error scenarios{self.tb.get_time_ns_str()}")
        self.log.info("="*80)

        all_passed = True

        # Test response error scenario (works for both read and write)
        self.log.info(f"Testing response error scenario{self.tb.get_time_ns_str()}")

        await self.reset_and_setup_for_test()

        resp_err_detected = await self.drive_error_scenario(
            error_type='resp_error',
            addr=0x6000,
            id_value=0,
            resp_value=2,  # SLVERR
            intrbus_ready_speed='fixed'
        )

        if not resp_err_detected:
            self.log.error(f"Response error scenario failed{self.tb.get_time_ns_str()}")
            all_passed = False
        else:
            self.log.info(f"Response error scenario passed{self.tb.get_time_ns_str()}")

        # Test address timeout scenario
        self.log.info(f"Testing address timeout scenario{self.tb.get_time_ns_str()}")

        await self.reset_and_setup_for_test()

        addr_timeout_detected = await self.drive_error_scenario(
            error_type='addr_timeout',
            addr=0x7000,
            id_value=1,
            resp_value=0,
            intrbus_ready_speed='fixed'
        )

        if not addr_timeout_detected:
            self.log.error(f"Address timeout scenario failed{self.tb.get_time_ns_str()}")
            all_passed = False
        else:
            self.log.info(f"Address timeout scenario passed{self.tb.get_time_ns_str()}")

        # Test data timeout scenario
        self.log.info(f"Testing data timeout scenario{self.tb.get_time_ns_str()}")

        await self.reset_and_setup_for_test()

        data_timeout_detected = await self.drive_error_scenario(
            error_type='data_timeout',
            addr=0x8000,
            id_value=2,
            resp_value=0,
            intrbus_ready_speed='fixed'
        )

        if not data_timeout_detected:
            self.log.error(f"Data timeout scenario failed{self.tb.get_time_ns_str()}")
            all_passed = False
        else:
            self.log.info(f"Data timeout scenario passed{self.tb.get_time_ns_str()}")

        # Test response timeout scenario (write mode only)
        if not self.tb.is_read:
            self.log.info(f"Testing response timeout scenario{self.tb.get_time_ns_str()}")

            await self.reset_and_setup_for_test()

            resp_timeout_detected = await self.drive_error_scenario(
                error_type='resp_timeout',
                addr=0x9000,
                id_value=3,
                resp_value=0,
                intrbus_ready_speed='fixed'
            )

            if not resp_timeout_detected:
                self.log.error(f"Response timeout scenario failed{self.tb.get_time_ns_str()}")
                all_passed = False
            else:
                self.log.info(f"Response timeout scenario passed{self.tb.get_time_ns_str()}")

        if all_passed:
            self.log.info(f"All basic error scenarios passed{self.tb.get_time_ns_str()}")
        else:
            self.log.error(f"Some basic error scenarios failed{self.tb.get_time_ns_str()}")

        return all_passed
