"""
AXI4 Slave Read Test Module

This module provides test methods for validating the AXI4 Slave Read module
by leveraging the user interface and AXI4 interface modules.
"""

from CocoTBFramework.tbclasses.tbbase import TBBase

# Import from our user interface include file
from .axi4_slave_rd_usr_intf_incl import (
    ErrorType, 
    generate_timeout_test_values, create_collision_test_matrix
)


class Axi4SlaveRdTests(TBBase):
    """
    Test implementation for the AXI4 Slave Read module.
    This class contains the actual test methods that validate
    the functionality of the AXI4 Slave Read module.
    """

    def __init__(self, dut, user_intf, axi4_intf):
        """
        Initialize the AXI4 Slave Read Tests.

        Args:
            dut: Device under test
            user_intf: User interface instance (Axi4SlaveRdUserIntf)
            axi4_intf: AXI4 interface instance (Axi4SlaveRdAxi4Intf)
        """
        super().__init__(dut)

        # Store the interfaces
        self.user_intf = user_intf
        self.axi4_intf = axi4_intf

        # Extract parameters from the DUT or use defaults
        self.id_width = int(getattr(dut, 'AXI_ID_WIDTH', 8))
        self.addr_width = int(getattr(dut, 'AXI_ADDR_WIDTH', 32))
        self.data_width = int(getattr(dut, 'AXI_DATA_WIDTH', 32))
        self.user_width = int(getattr(dut, 'AXI_USER_WIDTH', 1))
        self.timeout_ar = int(getattr(dut, 'TIMEOUT_AR', 1000))
        self.timeout_r = int(getattr(dut, 'TIMEOUT_R', 1000))

        # Calculate strobe width
        self.strb_width = self.data_width // 8

        # set the burst type
        self.burst = 0x1

        # Calculate size parameter based on data width
        self.dsize = 0  # Default to byte access
        temp_width = self.data_width // 8  # Convert to bytes
        while temp_width > 1:
            temp_width >>= 1
            self.dsize += 1

        # Test results tracking
        self.test_results = {}

    async def reset_dut(self):
        """Reset the DUT and all interfaces."""
        # Assert reset
        self.dut.aresetn.value = 0

        # Reset interfaces
        await self.user_intf.reset_interfaces()
        await self.axi4_intf.reset_interfaces()

        # Wait a few clock cycles
        await self.wait_clocks('aclk', 10)

        # Deassert reset
        self.dut.aresetn.value = 1

        # Wait for stabilization
        await self.wait_clocks('aclk', 10)

        self.log.info("DUT and interfaces reset")

    async def test_01_basic_read(self):
        """
        Test 01: Basic read transactions.

        Tests a representative number of reads with various delays.
        Verifies that responses match expected data.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 01: Basic Read Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Generate test addresses
        test_addresses = []
        for i in range(10):
            # Generate address 64-byte aligned
            addr = i * 256
            test_addresses.append(addr)

        # Track test status
        total_transactions = 0
        total_errors = 0

        # Iterate with various delays
        # randomizer options: 'fixed', 'always_ready', 'fast', 'slow'
        rand_keys = [
            ('always_ready', 'fixed'),
            # ('always_ready', 'always_ready'),
            # ('always_ready', 'fast'),
            # ('always_ready', 'slow')
            ]

        # Maximum ID value (for masking)
        max_id = (1 << self.id_width) - 1  # Typically 255 for 8-bit ID

        for j, (m_rand, s_rand) in enumerate(rand_keys):
            self.user_intf.set_error_readiness(m_rand)
            self.axi4_intf.set_m_axi_ar_timing(m_rand)
            self.axi4_intf.set_s_axi_r_timing(s_rand)

            # Send reads with different sizes and lengths
            for i, addr_pre in enumerate(test_addresses):
                addr = 0x10000 + (j*4096) + addr_pre # calculate the final address

                # With the fixed size from the interface:
                size = self.axi4_intf.dsize  # Use the fixed size from the interface
                length = i % 8  # Vary length between 0-7

                # Generate a unique ID for this transaction
                id_value = ((j * 10) + i) & max_id

                # Log transaction details for debugging
                self.log.info(f"Sending read: addr=0x{addr:X}, length={length}, id=0x{id_value:X}")

                # Send read request
                await self.axi4_intf.send_read(addr, length, id_value=id_value)

                # Count transactions
                total_transactions += 1

                # Brief delay between transactions
                await self.wait_clocks('aclk', 5)

        # Wait for all transactions to complete
        self.log.info("Waiting for all transactions to complete...")
        await self.wait_clocks('aclk', 100 + (total_transactions * 20))

        # Verify all transactions completed correctly
        for j, _ in enumerate(rand_keys):
            for i, _ in enumerate(test_addresses):
                id_value = ((j * 10) + i) & max_id
                
                # Verify data for this transaction
                if not self.axi4_intf.verify_response_data(id_value):
                    self.log.error(f"Data verification failed for ID={id_value:X}")
                    total_errors += 1

        # Log any errors from interfaces
        total_errors += self.user_intf.total_errors + self.axi4_intf.total_errors

        # Log test result
        if total_errors == 0:
            self.log.info(f"Basic read test PASSED - all {total_transactions} transactions had correct data")
        else:
            self.log.error(f"Basic read test FAILED with {total_errors} errors")

        # Store test results
        self.test_results['test_01_basic_read'] = (total_errors == 0)

        self.log.info(f"Test 01 Basic Read completed with {total_errors} errors")
        return total_errors == 0

    async def test_02_response_error_test(self):
        """
        Test 02: Response Error Test, test error responses.

        Tests error responses and ensures they show up correctly on the error interface.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 02: Response Error Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Set fast timing for clean test
        self.user_intf.set_error_readiness('fast_ready')
        self.axi4_intf.set_m_axi_ar_timing('fast')
        self.axi4_intf.set_s_axi_r_timing('fast')

        # Enable response error injection
        self.axi4_intf.configure_error_injection('resp', True, 1.0)  # Always inject errors
        await self.axi4_intf.start_error_injection()

        # Test cases
        test_cases = []

        # Standard read cases with different lengths
        test_cases.append((64, 0, 2, 1, f"Single beat response error"))
        test_cases.append((128, 3, 2, 1, f"4-beat burst response error"))
        test_cases.append((256, 7, 2, 1, f"8-beat burst response error"))

        total_errors = 0
        total_transactions = 0

        for addr, length, size, burst, description in test_cases:
            total_transactions += 1
            self.log.info(f"Running response error test: {description}")

            # Register expected error (SLVERR or DECERR)
            id_value = total_transactions
            self.user_intf.expect_error(id_value, ErrorType.R_RESP_ERROR)

            # Send read request
            await self.axi4_intf.send_read(addr, length, id_value=id_value)

            # Brief delay between transactions
            await self.wait_clocks('aclk', 100)

        # Wait for all transactions to complete and errors to be reported
        self.log.info("Waiting for all errors to be reported...")
        await self.wait_clocks('aclk', total_transactions * 200)

        # Verify error information
        self.log.info(f"Waiting for error reports...")
        await self.user_intf.wait_for_errors(total_transactions, 100000)

        # Verify right number of errors were detected
        error_count = self.user_intf.get_error_count(ErrorType.R_RESP_ERROR)
        if error_count != total_transactions:
            self.log.error(f"Error count mismatch: expected={total_transactions}, actual={error_count}")
            total_errors += 1

        # Add errors from interfaces
        total_errors += self.user_intf.total_errors + self.axi4_intf.total_errors

        # Store test results
        self.test_results['test_02_response_error_test'] = (total_errors == 0)

        self.log.info(f"Test 02 Response Error Test completed with {total_errors} errors")
        return total_errors == 0

    async def test_03_r_timeout_test(self):
        """
        Test 03: R Timeout Test, test R channel timeout detection.

        Issues a read with beats on the m_axi_ar channel, accepts it immediately,
        but delays responses on the s_axi_r channel to trigger timeout.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 03: R Timeout Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Set fast timing for AR channel, but slow for R channel
        self.user_intf.set_error_readiness('fast_ready')
        self.axi4_intf.set_m_axi_ar_timing('fast')

        # Generate timeout values to test around the configured timeout
        timeout_values = generate_timeout_test_values(self.timeout_r, 6)  # 6 test points

        total_errors = 0
        total_transactions = 0
        expected_timeouts = 0

        # Run tests with different timeout delays
        for r_timeout in timeout_values:
            total_transactions += 1

            # Create custom randomizer for this specific timeout
            if r_timeout >= self.timeout_r:
                # Should timeout
                expected_timeouts += 1
                self.user_intf.expect_error(total_transactions, ErrorType.R_TIMEOUT)

                # Set timing to trigger timeout
                self.axi4_intf.set_s_axi_r_timing('timeout')
                self.log.info(f"Testing R timeout: {r_timeout} clocks (should timeout)")
            else:
                # Should not timeout
                self.axi4_intf.set_s_axi_r_timing('slow')
                self.log.info(f"Testing R timeout: {r_timeout} clocks (should not timeout)")

            # Send multi-beat read transaction
            addr = 64 * total_transactions
            length = 3  # 4 beats
            size = 2    # 4 bytes per beat

            # Send read request
            await self.axi4_intf.send_read(addr, length, id_value=total_transactions)

            # Adequate delay for timeout to trigger or not
            await self.wait_clocks('aclk', r_timeout * 2)

        # Wait for all transactions to complete or timeout
        self.log.info("Waiting for all transactions to complete or timeout...")
        await self.wait_clocks('aclk', total_transactions * self.timeout_r * 3)

        # Verify R timeout errors were reported
        self.log.info("Waiting for error reports...")
        await self.user_intf.wait_for_errors(expected_timeouts, 100000)

        # Verify right number of R timeouts were detected
        r_timeout_count = self.user_intf.get_error_count(ErrorType.R_TIMEOUT)
        if r_timeout_count != expected_timeouts:
            self.log.error(f"R timeout count mismatch: expected={expected_timeouts}, actual={r_timeout_count}")
            total_errors += 1

        # Add errors from interfaces
        total_errors += self.user_intf.total_errors + self.axi4_intf.total_errors

        # Store test results
        self.test_results['test_03_r_timeout_test'] = (total_errors == 0)

        self.log.info(f"Test 03 R Timeout Test completed with {total_errors} errors")
        return total_errors == 0

    async def test_04_ar_timeout_test(self):
        """
        Test 04: AR Timeout Test, test AR channel timeout detection.

        Issues read requests but causes the AR channel to timeout
        by not accepting the requests.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 04: AR Timeout Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Set fast timing for R channel responses
        self.user_intf.set_error_readiness('fast_ready')
        self.axi4_intf.set_s_axi_r_timing('fast')

        # Generate timeout values to test around the configured timeout
        timeout_values = generate_timeout_test_values(self.timeout_ar, 6)  # 6 test points

        total_errors = 0
        total_transactions = 0
        expected_timeouts = 0

        # Run tests with different timeout delays
        for ar_timeout in timeout_values:
            total_transactions += 1

            # Configure for this specific timeout
            if ar_timeout >= self.timeout_ar:
                # Should timeout
                expected_timeouts += 1
                self.user_intf.expect_error(total_transactions, ErrorType.AR_TIMEOUT)

                # Configure error injection for AR timeout
                self.axi4_intf.configure_error_injection('ar_timeout', True, 1.0)  # 100% chance
                self.log.info(f"Testing AR timeout: {ar_timeout} clocks (should timeout)")
            else:
                # Should not timeout
                self.axi4_intf.configure_error_injection('ar_timeout', False)
                self.log.info(f"Testing AR timeout: {ar_timeout} clocks (should not timeout)")

            # Start error injection
            await self.axi4_intf.start_error_injection()

            # Send single-beat read transaction
            addr = 64 * total_transactions
            length = 0  # 1 beat
            size = 2    # 4 bytes per beat

            # Send read request
            await self.axi4_intf.send_read(addr, length, id_value=total_transactions)

            # Adequate delay for timeout to trigger or not
            await self.wait_clocks('aclk', ar_timeout * 2)

            # Disable error injection before next test
            self.axi4_intf.configure_error_injection('ar_timeout', False)

        # Wait for all transactions to complete or timeout
        self.log.info("Waiting for all transactions to complete or timeout...")
        await self.wait_clocks('aclk', total_transactions * self.timeout_ar * 3)

        # Verify AR timeout errors were reported
        self.log.info(f"Waiting for error reports...")
        await self.user_intf.wait_for_errors(expected_timeouts, 100000)

        # Verify right number of AR timeouts were detected
        ar_timeout_count = self.user_intf.get_error_count(ErrorType.AR_TIMEOUT)
        if ar_timeout_count != expected_timeouts:
            self.log.error(f"AR timeout count mismatch: expected={expected_timeouts}, actual={ar_timeout_count}")
            total_errors += 1

        # Add errors from interfaces
        total_errors += self.user_intf.total_errors + self.axi4_intf.total_errors

        # Store test results
        self.test_results['test_04_ar_timeout_test'] = (total_errors == 0)

        self.log.info(f"Test 04 AR Timeout Test completed with {total_errors} errors")
        return total_errors == 0

    async def test_05_collision_cases(self):
        """
        Test 05: Collision cases, test error collision reporting.

        Try to collide Response Error/RTO/ARTO to test that
        even if 2-3 of them happen at once, they all get reported.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 05: Collision Cases Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Set fast readiness for error reporting
        self.user_intf.set_error_readiness('fast_ready')

        # Create test matrix for error collisions
        collision_matrix = create_collision_test_matrix()

        total_errors = 0
        total_cases = 0

        # Run each collision test case
        for error_types in collision_matrix:
            total_cases += 1
            self.log.info(f"Testing error collision: {[ErrorType(et).name for et in error_types]}")

            # Configure error injection for this case
            self.axi4_intf.configure_error_injection('resp', ErrorType.R_RESP_ERROR in error_types, 1.0)
            self.axi4_intf.configure_error_injection('ar_timeout', ErrorType.AR_TIMEOUT in error_types, 1.0)
            self.axi4_intf.configure_error_injection('r_timeout', ErrorType.R_TIMEOUT in error_types, 1.0)

            # Start error injection
            await self.axi4_intf.start_error_injection()

            # For each error type, expect it to be reported
            for error_type in error_types:
                self.user_intf.expect_error(total_cases, error_type)

            # Send read transaction
            addr = 64 * total_cases
            length = 1  # 2 beats
            size = 2    # 4 bytes per beat

            # Send read request
            await self.axi4_intf.send_read(addr, length, id_value=total_cases)

            # Wait for errors to be reported
            self.log.info("Waiting for collision errors to be reported...")
            await self.wait_clocks('aclk', 1000)

            # Verify that the expected error types were detected
            success = await self.user_intf.verify_collision_behavior(error_types, 2000)
            if not success:
                self.log.error(f"Collision test failed for types: {[ErrorType(et).name for et in error_types]}")
                total_errors += 1

            # Disable error injection before next test
            self.axi4_intf.configure_error_injection('resp', False)
            self.axi4_intf.configure_error_injection('ar_timeout', False)
            self.axi4_intf.configure_error_injection('r_timeout', False)

            # Delay between cases
            await self.wait_clocks('aclk', 1000)

        # Add errors from interfaces
        total_errors += self.user_intf.total_errors + self.axi4_intf.total_errors

        # Store test results
        self.test_results['test_05_collision_cases'] = (total_errors == 0)

        self.log.info(f"Test 05 Collision Cases completed with {total_errors} errors")
        return total_errors == 0

    def get_test_results(self):
        """
        Get a summary of all test results.

        Returns:
            Dict with test results
        """
        return self.test_results

    def all_tests_passed(self):
        """
        Check if all tests passed.

        Returns:
            True if all tests passed, False otherwise
        """
        return all(self.test_results.values())