"""
Error scenario test class for AXI Error Monitor.

This module provides tests for error detection and reporting in the AXI Error Monitor
Base module, focusing on timeout detection and error responses.
"""

from .axi_errmon_base_test import AXIErrorMonBaseTest


class AXIErrorMonErrorTest(AXIErrorMonBaseTest):
    """
    Error tests for AXI Error Monitor.
    Tests error detection, reporting, and recovery.
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
        Run all error tests

        Returns:
            True if all tests passed, False otherwise
        """
        self.log.info("+"*80)
        self.log.info(f"Running error tests{self.tb.get_time_ns_str()}")
        self.log.info("+"*80)

        # Run timeout tests
        addr_timeout_passed = await self.test_addr_timeout()
        data_timeout_passed = await self.test_data_timeout()

        # Run response timeout test (write mode only)
        if not self.tb.is_read:
            resp_timeout_passed = await self.test_resp_timeout()
        else:
            resp_timeout_passed = True  # Skip for read mode

        # Run response error test
        resp_error_passed = await self.test_resp_error()

        # # Run multi-error reporting test
        # multi_error_passed = await self.test_multi_error_reporting()

        # Run edge case completion test
        edge_case_passed = await self.test_edge_case_completion()

        # Run recovery test
        recovery_passed = await self.test_recovery_after_errors()

        # Report results
        all_passed = (
            addr_timeout_passed and
            data_timeout_passed and
            resp_timeout_passed and
            resp_error_passed and
            # multi_error_passed and
            edge_case_passed and
            recovery_passed
        )

        if all_passed:
            self.log.info(f"All error tests passed{self.tb.get_time_ns_str()}")
        else:
            self.log.error(f"Some error tests failed{self.tb.get_time_ns_str()}")

        return all_passed

    async def test_addr_timeout(self):
        """
        Test address timeout detection

        This test verifies that the monitor correctly detects and reports
        timeout conditions in the address channel.

        Returns:
            True if test passed, False otherwise
        """
        self.log.info(f"{'=' * 80}")
        self.log.info(f"Testing address timeout detection{self.tb.get_time_ns_str()}")
        self.log.info(f"{'=' * 80}")

        # Reset and setup for clean test state
        await self.reset_and_setup_for_test()

        # Drive an address timeout scenario
        result = await self.drive_error_scenario(
            error_type='addr_timeout',
            addr=0x7000,
            id_value=0
        )

        # Check that error was detected with the correct type
        if not result:
            self.log.error(f"Address timeout test failed{self.tb.get_time_ns_str()}")
            return False

        self.log.info(f"Address timeout test passed successfully{self.tb.get_time_ns_str()}")
        return True

    async def test_data_timeout(self):
        """
        Test data timeout detection

        This test verifies that the monitor correctly detects and reports
        timeout conditions in the data channel.

        Returns:
            True if test passed, False otherwise
        """
        self.log.info(f"{'=' * 80}")
        self.log.info(f"Testing data timeout detection{self.tb.get_time_ns_str()}")
        self.log.info(f"{'=' * 80}")

        # Reset and setup for clean test state
        await self.reset_and_setup_for_test()

        # Drive a data timeout scenario
        result = await self.drive_error_scenario(
            error_type='data_timeout',
            addr=0x7100,
            id_value=1
        )

        # Check that error was detected with the correct type
        if not result:
            self.log.error(f"Data timeout test failed{self.tb.get_time_ns_str()}")
            return False

        self.log.info(f"Data timeout test passed successfully{self.tb.get_time_ns_str()}")
        return True

    async def test_resp_timeout(self):
        """
        Test response timeout detection (write mode only)

        This test verifies that the monitor correctly detects and reports
        timeout conditions in the response channel.

        Returns:
            True if test passed, False otherwise
        """
        # Skip for read mode
        if self.tb.is_read:
            self.log.info(f"Skipping response timeout test for read mode{self.tb.get_time_ns_str()}")
            return True

        self.log.info(f"{'=' * 80}")
        self.log.info(f"Testing response timeout detection{self.tb.get_time_ns_str()}")
        self.log.info(f"{'=' * 80}")

        # Reset and setup for clean test state
        await self.reset_and_setup_for_test()

        # Drive a response timeout scenario
        slverr_passed = await self.drive_error_scenario(
            error_type='resp_timeout',
            addr=0x7200,
            id_value=2
        )

        # Check that error was detected with the correct type
        if not slverr_passed:
            self.log.error(f"Response timeout test failed{self.tb.get_time_ns_str()}")
            return False

        self.log.info(f"Response timeout test passed successfully{self.tb.get_time_ns_str()}")
        return True

    async def test_resp_error(self):
        """
        Test response error detection

        This test verifies that the monitor correctly detects and reports
        error responses (SLVERR/DECERR).

        Returns:
            True if test passed, False otherwise
        """
        self.log.info(f"{'=' * 80}")
        self.log.info(f"Testing response error detection{self.tb.get_time_ns_str()}")
        self.log.info(f"{'=' * 80}")

        # Reset and setup for clean test state
        await self.reset_and_setup_for_test()

        # Test both error types
        error_types = [
            (2, "SLVERR"),  # SLVERR = 2
            (3, "DECERR")   # DECERR = 3
        ]

        all_passed = True
        id_value = 0

        for error_code, error_name in error_types:
            self.log.info(f"Testing {error_name} response error{self.tb.get_time_ns_str()}")

            # Drive a response error scenario
            slverr_passed = await self.drive_error_scenario(
                error_type='resp_error',
                addr=0x7300 + (error_code * 0x100),
                id_value=id_value,
                resp_value=error_code
            )

            # Check that error was detected with the correct type
            if not slverr_passed:
                self.log.error(f"{error_name} response error test failed{self.tb.get_time_ns_str()}")
                all_passed = False

        if all_passed:
            self.log.info(f"Response error test passed successfully{self.tb.get_time_ns_str()}")

        return all_passed

    async def test_timer_behavior(self):
        """
        Test timer behavior

        This test verifies the timer initialization and counting behavior,
        including the countdown from MAX value.

        Returns:
            True if test passed, False otherwise
        """
        self.log.info(f"{'=' * 80}")
        self.log.info(f"Testing timer behavior{self.tb.get_time_ns_str()}")
        self.log.info(f"{'=' * 80}")

        # Test the timer countdown behavior
        result = await self.test_timer_countdown()

        if not result:
            self.log.error(f"Timer behavior test failed{self.tb.get_time_ns_str()}")
            return False

        self.log.info(f"Timer behavior test passed successfully{self.tb.get_time_ns_str()}")
        return True