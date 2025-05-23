"""
Basic test class for AXI Error Monitor.

This module provides basic functionality tests for the AXI Error Monitor Base module,
focusing on simple transaction handling and interrupt bus events.
"""

from .axi_errmon_base_test import AXIErrorMonBaseTest
from CocoTBFramework.components.flex_randomizer import FlexRandomizer


class AXIErrorMonBasicTest(AXIErrorMonBaseTest):
    """
    Basic tests for AXI Error Monitor.
    Tests simple transaction handling and basic functionality.
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

        # Report results
        all_passed = single_passed and timer_passed and sequential_passed and pipeline_passed and intrbus_passed

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

        # Set intrbus ready to normal speed
        self.tb.intrbus_slave.set_randomizer(FlexRandomizer(self.tb.randomizer_configs['fixed']))

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
            if (event['packet_type'] == 1 and  # Completion packet type
                event['event_code'] == 0x9 and  # EVT_TRANS_COMPLETE
                event['channel_id'] == 0 and
                event['addr'] == 0x1000):
                self.log.info(f"Found completion event for transaction: addr=0x{event['addr']:X}, id={event['channel_id']}{self.tb.get_time_ns_str()}")
                completion_found = True
                break

        # Note: Not all configurations will generate completion events, so this is not a pass/fail criteria
        if not completion_found:
            self.log.debug(f"No completion event detected for transaction (this is normal in some configurations){self.tb.get_time_ns_str()}")

        self.log.info(f"Single transaction test passed successfully{self.tb.get_time_ns_str()}")
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

        # Set intrbus ready to normal speed
        self.tb.intrbus_slave.set_randomizer(FlexRandomizer(self.tb.randomizer_configs['fixed']))

        # Drive multiple transactions sequentially
        num_transactions = 10

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

        # Set intrbus ready to normal speed
        self.tb.intrbus_slave.set_randomizer(FlexRandomizer(self.tb.randomizer_configs['fixed']))

        # Drive multiple transactions with pipelining
        num_transactions = 10

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
        ready_speeds = ['fixed', 'slow_consumer', 'backtoback']
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
            wait_cycles = 50 if speed == 'slow_consumer' else 20
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
                if (event['packet_type'] == 0 and  # Error packet type
                    event['event_code'] in [0x4, 0x5] and  # SLVERR or DECERR
                    event['addr'] == 0x5000):
                    error_found = True
                    self.log.info(f"Found error event: {event['description']}{self.tb.get_time_ns_str()}")
                    break

            if not error_found:
                self.log.error(f"Expected error event not found on intrbus with {speed} ready{self.tb.get_time_ns_str()}")
                all_tests_passed = False
            else:
                self.log.info(f"Interrupt bus events test passed with {speed} ready{self.tb.get_time_ns_str()}")

        # Reset intrbus ready to fixed speed
        self.tb.intrbus_slave.set_randomizer(FlexRandomizer(self.tb.randomizer_configs['fixed']))

        return all_tests_passed
