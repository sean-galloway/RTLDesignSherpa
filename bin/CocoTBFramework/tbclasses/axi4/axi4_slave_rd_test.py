"""
AXI4 Slave Read Test Module

This module provides test methods for validating the AXI4 Slave Read module
by leveraging the master interface and memory interface modules.
"""

from enum import IntFlag
import cocotb

from CocoTBFramework.tbclasses.tbbase import TBBase

# Error type definitions for slave module
class ErrorType(IntFlag):
    """Error types for AXI4 slave read module"""
    AR_TIMEOUT = 0b0001  # Bit 0: Address Read timeout
    R_TIMEOUT = 0b0010   # Bit 1: Read Data timeout
    R_RESP_ERROR = 0b0100  # Bit 2: Read response error (SLVERR, DECERR)


class Axi4SlaveRdTests(TBBase):
    """
    Test implementation for the AXI4 Slave Read module.
    This class contains the actual test methods that validate
    the functionality of the AXI4 Slave Read module.
    """

    def __init__(self, dut, axi4_intf, user_intf):
        """
        Initialize the AXI4 Slave Read Tests.

        Args:
            dut: Device under test
            axi4_intf: Master interface instance (Axi4SlaveRdMasterIntf)
            user_intf: Memory interface instance (Axi4SlaveRdMemIntf)
        """
        super().__init__(dut)

        # Store the interfaces
        self.axi4_intf = axi4_intf
        self.user_intf = user_intf

        # Extract parameters from the DUT or use defaults
        self.id_width = int(getattr(dut, 'AXI_ID_WIDTH', 8))
        self.addr_width = int(getattr(dut, 'AXI_ADDR_WIDTH', 32))
        self.data_width = int(getattr(dut, 'AXI_DATA_WIDTH', 32))
        self.user_width = int(getattr(dut, 'AXI_USER_WIDTH', 1))
        self.timeout_ar = int(getattr(dut, 'TIMEOUT_AR', 1000))
        self.timeout_r = int(getattr(dut, 'TIMEOUT_R', 1000))

        # Set the max boundary
        self.boundary_4k = 0xFFF

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
        await self.axi4_intf.reset_interfaces()
        await self.user_intf.reset_interfaces()

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

        Tests a representative number of reads with different
        data patterns to verify basic slave read functionality.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 01: Basic Read Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Use a large alignment mask to avoid splitting
        self.axi4_intf.set_dut_alignment_mask(self.boundary_4k)

        # Initialize memory with test patterns
        await self.user_intf.initialize_memory_pattern()

        # Set master timing to normal
        self.axi4_intf.set_m_axi_ar_timing('fast')
        self.axi4_intf.set_m_axi_r_timing('fast')

        # Track test status
        total_transactions = 0
        total_errors = 0

        # Generate test addresses
        test_addresses = []
        for i in range(10):
            # Generate addresses at 64-byte intervals
            addr = i * 64
            test_addresses.append(addr)

        # Run tests with different burst lengths
        for length in [0, 1, 3, 7, 15]:
            self.log.info(f"Testing burst length {length+1}")

            # For each address
            for i, addr in enumerate(test_addresses):
                # Generate a unique ID
                id_value = i + (length * 16)

                # Calculate expected data from memory
                expected_data = []
                for j in range(length + 1):
                    beat_addr = addr + (j * self.strb_width)
                    expected_data.append((beat_addr + 0xA5A5A5A5) & 0xFFFFFFFF)

                # Send read request to memory interface
                self.user_intf.expect_read(addr, length, id_value, expected_data)

                # Send read request through master interface
                result = await self.axi4_intf.read(addr, length=length, id_value=id_value)

                # Verify result
                if not result or result.get('id') != id_value:
                    self.log.error(f"Read transaction failed or ID mismatch: addr=0x{addr:X}, length={length}")
                    total_errors += 1
                    continue

                # Verify data
                received_data = result.get('data', [])
                if len(received_data) != length + 1:
                    self.log.error(f"Read data length mismatch: expected={length+1}, received={len(received_data)}")
                    total_errors += 1
                    continue

                # Compare data values
                for j, (expected, received) in enumerate(zip(expected_data, received_data)):
                    if expected != received:
                        self.log.error(f"Read data mismatch at beat {j}: expected=0x{expected:X}, received=0x{received:X}")
                        total_errors += 1

                # Count successful transaction
                total_transactions += 1

                # Brief delay between transactions
                await self.wait_clocks('aclk', 5)

        # Log any errors from interfaces
        total_errors += self.axi4_intf.total_errors + self.user_intf.total_errors

        # Log test result
        if total_errors == 0:
            self.log.info(f"Basic read test PASSED - all {total_transactions} transactions successful")
        else:
            self.log.error(f"Basic read test FAILED with {total_errors} errors")

        # Store test results
        self.test_results['test_01_basic_read'] = (total_errors == 0)

        return total_errors == 0

    async def test_02_concurrent_reads(self):
        """
        Test 02: Concurrent read transactions with different IDs.

        Tests multiple outstanding read transactions with different IDs
        to ensure proper handling and responses.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 02: Concurrent Reads Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Initialize memory with test patterns
        await self.user_intf.initialize_memory_pattern()

        # Set master timing to normal
        self.axi4_intf.set_m_axi_ar_timing('fast')
        self.axi4_intf.set_m_axi_r_timing('fast')

        # Track test status
        total_errors = 0
        pending_reads = {}

        # Number of concurrent transactions
        num_concurrent = 8

        # Generate test cases with different attributes
        test_cases = []
        for i in range(num_concurrent):
            # Vary address, length, and ID
            addr = i * 256
            length = (i % 4) * 2  # 0, 2, 4, 6
            id_value = i + 16

            test_cases.append((addr, length, id_value))

            # Calculate expected data from memory
            expected_data = []
            for j in range(length + 1):
                beat_addr = addr + (j * self.strb_width)
                expected_data.append((beat_addr + 0xA5A5A5A5) & 0xFFFFFFFF)

            # Prepare memory interface
            self.user_intf.expect_read(addr, length, id_value, expected_data)

        # Send all read requests without waiting for completion
        for addr, length, id_value in test_cases:
            # Send read request through master interface (non-blocking)
            read_task = cocotb.start_soon(self.axi4_intf.read(addr, length=length, id_value=id_value))
            pending_reads[id_value] = read_task

            # Short delay between requests
            await self.wait_clocks('aclk', 2)

        # Wait for all reads to complete
        self.log.info(f"Waiting for {len(pending_reads)} concurrent reads to complete")

        for id_value, task in pending_reads.items():
            result = await task

            # Verify result
            if not result or result.get('id') != id_value:
                self.log.error(f"Read transaction failed or ID mismatch for ID={id_value}")
                total_errors += 1
                continue

            # Get expected data for this ID
            test_case = next((tc for tc in test_cases if tc[2] == id_value), None)
            if not test_case:
                self.log.error(f"Test case for ID={id_value} not found")
                total_errors += 1
                continue

            addr, length, _ = test_case

            # Verify data length
            received_data = result.get('data', [])
            if len(received_data) != length + 1:
                self.log.error(f"Read data length mismatch for ID={id_value}: expected={length+1}, received={len(received_data)}")
                total_errors += 1
                continue

            # Calculate and compare expected data
            for j in range(length + 1):
                beat_addr = addr + (j * self.strb_width)
                expected = (beat_addr + 0xA5A5A5A5) & 0xFFFFFFFF

                if j < len(received_data) and received_data[j] != expected:
                    self.log.error(f"Read data mismatch for ID={id_value} at beat {j}: expected=0x{expected:X}, received=0x{received_data[j]:X}")
                    total_errors += 1

        # Log any errors from interfaces
        total_errors += self.axi4_intf.total_errors + self.user_intf.total_errors

        # Log test result
        if total_errors == 0:
            self.log.info(f"Concurrent reads test PASSED - all {len(pending_reads)} transactions successful")
        else:
            self.log.error(f"Concurrent reads test FAILED with {total_errors} errors")

        # Store test results
        self.test_results['test_02_concurrent_reads'] = (total_errors == 0)

        return total_errors == 0

    async def test_03_error_response(self):
        """
        Test 03: Error response handling.

        Tests that the slave correctly generates error responses
        for invalid read requests.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 03: Error Response Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Set memory interface to generate errors
        self.user_intf.set_error_mode(True)

        # Set master timing to normal
        self.axi4_intf.set_m_axi_ar_timing('fast')
        self.axi4_intf.set_m_axi_r_timing('fast')

        # Track test status
        total_errors = 0
        total_transactions = 0

        # Test cases for error responses (invalid addresses)
        error_addresses = [0xDEADBEEF, 0xFFFFFFFF, 0xBAD00BAD]

        for i, addr in enumerate(error_addresses):
            id_value = 0x80 + i  # Use distinct IDs
            length = i % 4  # Mix of burst lengths

            # Expect error response in memory interface
            self.user_intf.expect_error_read(addr, length, id_value)

            # Send read request
            self.log.info(f"Sending read request to invalid address 0x{addr:X}")
            result = await self.axi4_intf.read(addr, length=length, id_value=id_value)

            # Verify error response
            if not result:
                self.log.error(f"Read transaction failed to complete: addr=0x{addr:X}, ID={id_value}")
                total_errors += 1
                continue

            # Check response code in each data beat
            received_data = result.get('data', [])
            all_error_responses = True

            for j, rdata in enumerate(received_data):
                resp = result.get('responses', [])[j].rresp if j < len(result.get('responses', [])) else None
                if resp not in [2, 3]:  # Not SLVERR or DECERR
                    self.log.error(f"Expected error response for beat {j}, got {resp}")
                    all_error_responses = False
                    total_errors += 1

            if all_error_responses:
                self.log.info(f"Received correct error responses for addr=0x{addr:X}")
                total_transactions += 1

            # Brief delay between transactions
            await self.wait_clocks('aclk', 10)

        # Log any errors from interfaces
        total_errors += self.axi4_intf.total_errors + self.user_intf.total_errors

        # Log test result
        if total_errors == 0:
            self.log.info(f"Error response test PASSED - all {total_transactions} transactions returned error responses")
        else:
            self.log.error(f"Error response test FAILED with {total_errors} errors")

        # Store test results
        self.test_results['test_03_error_response'] = (total_errors == 0)

        # Disable error mode for subsequent tests
        self.user_intf.set_error_mode(False)

        return total_errors == 0

    async def test_04_timeout_handling(self):
        """
        Test 04: Timeout handling in AXI slave.

        Tests that the slave correctly handles timeouts on R channel
        responses when memory interface is slow to respond.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 04: Timeout Handling Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Set memory interface to introduce delays (simulate slow memory)
        self.user_intf.set_delay_mode(True, self.timeout_r * 2)  # Set delay longer than R timeout

        # Set master timing to normal
        self.axi4_intf.set_m_axi_ar_timing('fast')
        self.axi4_intf.set_m_axi_r_timing('fast')

        # Track test status
        total_errors = 0
        total_transactions = 0

        # Track timeout error detection
        detected_timeout = False

        # Test case
        addr = 0x1000
        length = 3
        id_value = 0x42

        # Send read request
        self.log.info(f"Sending read request that will timeout: addr=0x{addr:X}")

        # Start read request
        read_task = cocotb.start_soon(self.axi4_intf.read(addr, length=length, id_value=id_value))

        # Wait for error monitoring to detect timeout
        for _ in range(self.timeout_r * 3):  # Wait up to 3x timeout period
            # Check if error monitor detected R timeout
            if self.axi4_intf.check_for_error(ErrorType.R_TIMEOUT):
                detected_timeout = True
                self.log.info(f"Detected R timeout for addr=0x{addr:X}")
                break

            await self.wait_clocks('aclk', 1)

        # Try to get result (may fail due to timeout)
        try:
            result = await read_task

            # If we got a response, verify it completes the transaction
            if result and result.get('id') == id_value:
                self.log.info(f"Read transaction completed despite timeout: addr=0x{addr:X}")
                # This is acceptable if timeout handling allows transaction to complete
                total_transactions += 1
            else:
                self.log.warning(f"Read transaction returned unexpected result after timeout")
        except Exception as e:
            self.log.info(f"Read transaction was cancelled as expected: {str(e)}")

        # Verify timeout was detected
        if not detected_timeout:
            self.log.error(f"Failed to detect R timeout")
            total_errors += 1
        else:
            total_transactions += 1

        # Log any errors from interfaces
        total_errors += self.axi4_intf.total_errors + self.user_intf.total_errors

        # Log test result
        if total_errors == 0:
            self.log.info(f"Timeout handling test PASSED - detected timeout as expected")
        else:
            self.log.error(f"Timeout handling test FAILED with {total_errors} errors")

        # Store test results
        self.test_results['test_04_timeout_handling'] = (total_errors == 0)

        # Disable delay mode for subsequent tests
        self.user_intf.set_delay_mode(False)

        return total_errors == 0

    async def test_05_performance(self):
        """
        Test 05: Performance assessment with back-to-back transactions.

        Tests the performance of the slave read module with
        back-to-back read transactions of different sizes.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 05: Performance Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Initialize memory with test patterns
        await self.user_intf.initialize_memory_pattern()

        # Set master to maximum performance
        self.axi4_intf.set_m_axi_ar_timing('always_ready')
        self.axi4_intf.set_m_axi_r_timing('always_ready')

        # Track test status
        total_errors = 0
        total_transactions = 0
        total_data_beats = 0
        start_time = cocotb.utils.get_sim_time('ns')

        # Define test patterns
        # List of (num_transactions, burst_length) pairs
        test_patterns = [
            (10, 0),     # 10 single-beat reads
            (5, 3),      # 5 4-beat reads
            (3, 7),      # 3 8-beat reads
            (2, 15),     # 2 16-beat reads
            (1, 255)     # 1 256-beat read
        ]

        # Run performance test with each pattern
        base_addr = 0x1000
        for pattern_idx, (num_txn, burst_len) in enumerate(test_patterns):
            pattern_start_time = cocotb.utils.get_sim_time('ns')
            pattern_beats = 0

            self.log.info(f"Running pattern {pattern_idx+1}: {num_txn} transactions with burst length {burst_len+1}")

            # Define list to hold all tasks
            read_tasks = []

            # Start all transactions
            for i in range(num_txn):
                addr = base_addr + (pattern_idx * 0x1000) + (i * 0x100)
                id_value = 0x20 + (pattern_idx * 16) + i

                # Prepare memory interface
                expected_data = []
                for j in range(burst_len + 1):
                    beat_addr = addr + (j * self.strb_width)
                    expected_data.append((beat_addr + 0xA5A5A5A5) & 0xFFFFFFFF)

                self.user_intf.expect_read(addr, burst_len, id_value, expected_data)

                # Start read task
                task = cocotb.start_soon(self.axi4_intf.read(addr, length=burst_len, id_value=id_value))
                read_tasks.append(task)

                # Track expected data beats
                pattern_beats += burst_len + 1

                # No delay between starting transactions

            # Wait for all transactions to complete
            for idx, task in enumerate(read_tasks):
                result = await task

                if not result:
                    self.log.error(f"Read transaction {idx} failed in pattern {pattern_idx+1}")
                    total_errors += 1
                    continue

                # Verify data length
                if len(result.get('data', [])) != burst_len + 1:
                    self.log.error(f"Read data length mismatch: expected={burst_len+1}, received={len(result.get('data', []))}")
                    total_errors += 1

                total_transactions += 1

            # Calculate pattern performance
            pattern_end_time = cocotb.utils.get_sim_time('ns')
            pattern_duration = pattern_end_time - pattern_start_time

            if pattern_duration > 0:
                beats_per_ns = pattern_beats / pattern_duration
                self.log.info(f"Pattern {pattern_idx+1} performance: {beats_per_ns:.3f} beats/ns ({pattern_beats} beats in {pattern_duration:.1f} ns)")

            # Update totals
            total_data_beats += pattern_beats

        # Calculate overall performance
        end_time = cocotb.utils.get_sim_time('ns')
        duration = end_time - start_time

        if duration > 0:
            overall_beats_per_ns = total_data_beats / duration
            self.log.info(f"Overall performance: {overall_beats_per_ns:.3f} beats/ns ({total_data_beats} beats in {duration:.1f} ns)")

        # Log any errors from interfaces
        total_errors += self.axi4_intf.total_errors + self.user_intf.total_errors

        # Log test result
        if total_errors == 0:
            self.log.info(f"Performance test PASSED - all {total_transactions} transactions successful")
        else:
            self.log.error(f"Performance test FAILED with {total_errors} errors")

        # Store test results
        self.test_results['test_05_performance'] = (total_errors == 0)

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
