"""
Basic test class for AXI Error Monitor.

This module provides basic functionality tests for the AXI Error Monitor Base module,
focusing on simple transaction handling.
"""

from .axi_errmon_base_test import AXIErrorMonBaseTest


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

        # Report results
        all_passed = single_passed and timer_passed and sequential_passed and pipeline_passed

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

        # Clear any previous errors
        self.tb.errors_detected = []

        # Drive a single transaction
        transaction = await self.drive_basic_transaction(
            addr=0x1000,
            id_value=0,
            data_value=0xABCD1234,
            resp_value=0,  # OKAY
            control_ready=False,  # Use default ready behavior
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

        # Clear any previous errors
        self.tb.errors_detected = []

        # Drive multiple transactions sequentially
        num_transactions = 10

        for i in range(num_transactions):
            addr = 0x2000 + (i * 0x100)
            id_value = i % self.tb.channels
            data_value = 0xA0000000 | i

            transaction = await self.drive_basic_transaction(
                addr=addr,
                id_value=id_value,
                data_value=data_value,
                resp_value=0,  # OKAY
                control_ready=False,  # Use default ready behavior
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

        # Clear any previous errors
        self.tb.errors_detected = []

        # Drive multiple transactions with pipelining
        num_transactions = 10

        for i in range(num_transactions):
            addr = 0x3000 + (i * 0x100)
            id_value = i % self.tb.channels
            data_value = 0xB0000000 | i

            transaction = await self.drive_basic_transaction(
                addr=addr,
                id_value=id_value,
                data_value=data_value,
                resp_value=0,  # OKAY
                control_ready=False,  # Use default ready behavior
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