"""
AXI4 Master Write Test Module

This module provides test methods for validating the AXI4 Master Write module
by leveraging the fub interface and AXI4 interface modules.
"""

from CocoTBFramework.tbclasses.tbbase import TBBase

# Import from our fub interface include file
from .axi4_master_wr_fub_intf_incl import (
    ErrorInfo, ErrorType,
    generate_timeout_test_values, create_collision_test_matrix
)


class Axi4MasterWrTests(TBBase):
    """
    Test implementation for the AXI4 Master Write module.
    This class contains the actual test methods that validate
    the functionality of the AXI4 Master Write module.
    """

    def __init__(self, dut, fub_intf, axi4_intf):
        """
        Initialize the AXI4 Master Write Tests.

        Args:
            dut: Device under test
            fub_intf: Fub interface instance (Axi4MasterWrFubIntf)
            axi4_intf: AXI4 interface instance (Axi4MasterWrAxi4Intf)
        """
        super().__init__(dut)

        # Store the interfaces
        self.fub_intf = fub_intf
        self.axi4_intf = axi4_intf

        # Extract parameters from the DUT or use defaults
        self.id_width = int(getattr(dut, 'AXI_ID_WIDTH', 8))
        self.addr_width = int(getattr(dut, 'AXI_ADDR_WIDTH', 32))
        self.data_width = int(getattr(dut, 'AXI_DATA_WIDTH', 32))
        self.fub_width = int(getattr(dut, 'AXI_FUB_WIDTH', 1))
        self.timeout_aw = int(getattr(dut, 'TIMEOUT_AW', 1000))
        self.timeout_w = int(getattr(dut, 'TIMEOUT_W', 1000))
        self.timeout_b = int(getattr(dut, 'TIMEOUT_B', 1000))

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

        # set up test boundaries
        self.boundary_4k = 0xFFF

        # Test results tracking
        self.test_results = {}

    async def reset_dut(self):
        """Reset the DUT and all interfaces."""
        # Assert reset
        self.dut.aresetn.value = 0

        # Reset interfaces
        await self.fub_intf.reset_interfaces()
        await self.axi4_intf.reset_interfaces()

        # Wait a few clock cycles
        await self.wait_clocks('aclk', 10)

        # Deassert reset
        self.dut.aresetn.value = 1

        # Wait for stabilization
        await self.wait_clocks('aclk', 10)

        self.log.info("DUT and interfaces reset")

    async def test_01_basic_write(self):
        """
        Test 01: Basic write transactions without splitting.

        Tests a representative number of writes with alignment mask
        set at different places. None of these should split.
        Verify the fub_split interface always shows 1.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 01: Basic Write Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Use a large alignment mask to avoid splitting
        self.axi4_intf.set_dut_alignment_mask(self.boundary_4k)

        # Generate test addresses at different positions
        test_addresses = []
        for i in range(10):
            # Generate address 64-byte aligned
            addr = i * 256
            test_addresses.append(addr)

        # Track test status
        total_transactions = 0
        total_errors = 0
        expected_splits = []  # List to track all expected split counts

        # Iterate with various delays
        # randomizer: split/error options: 'fixed', 'always_ready', 'fast_ready', 'slow_ready'
        #             aw/w/b options: 'fixed', 'always_ready', 'fast', 'slow'
        rand_keys = [
            ('always_ready', 'fixed'),
            ('always_ready', 'always_ready'),
            ('always_ready', 'fast'),
            ('always_ready', 'slow')
        ]

        # Maximum ID value (for masking)
        max_id = (1 << self.id_width) - 1  # Typically 255 for 8-bit ID

        for j, (split_rand, axi_rand) in enumerate(rand_keys):
            self.fub_intf.set_split_readiness(split_rand)
            self.fub_intf.set_error_readiness(split_rand)
            self.axi4_intf.set_fub_aw_timing(axi_rand)
            self.axi4_intf.set_fub_w_timing(axi_rand)
            self.axi4_intf.set_m_axi_b_timing(axi_rand)

            # Send writes with different sizes and lengths
            for i, addr_pre in enumerate(test_addresses):
                addr = 0x10000 + (j*4096) + addr_pre # calculate the final address

                # With the fixed size from the interface:
                size = self.axi4_intf.dsize  # Use the fixed size from the interface
                bytes_per_beat = 1 << size  # This will be 4 bytes for a 32-bit data bus
                length = i

                # Generate a unique ID for this transaction
                id_value = ((j * 10) + i) & max_id

                # Generate test data based on address
                data = [(addr + 0xA0000000 + (0x1000 * beat)) & 0xFFFFFFFF for beat in range(length + 1)]

                # Make sure no split occurs (check address vs boundary)
                boundary_mask = self.boundary_4k
                boundary_size = boundary_mask + 1

                # Calculate the end address
                end_addr = addr + (bytes_per_beat * (length + 1)) - 1

                # Check which boundary segments the transaction covers
                start_segment = addr // boundary_size
                end_segment = end_addr // boundary_size
                expected_split_count = 1 + (end_segment - start_segment)

                # For basic test, verify that expected_split_count is 1 (no splitting)
                if expected_split_count != 1:
                    self.log.error(f"Test setup error: Transaction would split - addr=0x{addr:X}, length={length}, end=0x{end_addr:X}")
                    self.log.error(f"  Start segment=0x{start_segment:X}, end segment=0x{end_segment:X}")
                    total_errors += 1
                    continue

                # Register expected transaction and save for later verification
                self.fub_intf.expect_split(id_value, expected_split_count)
                expected_splits.append((id_value, expected_split_count))

                # Log transaction details for debugging
                self.log.info(f"Sending write: addr=0x{addr:X}, length={length}, id=0x{id_value:X}, expected_splits={expected_split_count}")

                # Send write request
                await self.axi4_intf.send_write(addr, data, length, id_value=id_value)

                # Count transactions
                total_transactions += 1

                # Brief delay between transactions
                await self.wait_clocks('aclk', 5)

        # Wait for all transactions to complete
        self.log.info("Waiting for all transactions to complete...")
        await self.wait_clocks('aclk', 100)

        # Verify split information
        timeout_ns = 100000 + (total_transactions * 1000)
        if not await self.fub_intf.wait_for_splits(total_transactions, timeout_ns):
            self.log.error(f"Not all split notifications were received: expected {total_transactions}")
            total_errors += 1

        # Verify each split notification had the expected count
        for id_value, expected_count in expected_splits:
            # Check that the expected split count matches what was received
            if not self.fub_intf.verify_split_count(id_value, expected_count):
                self.log.error(f"Split count mismatch for ID=0x{id_value:X}: expected={expected_count}")
                total_errors += 1

        # Log any errors from interfaces
        total_errors += self.fub_intf.total_errors + self.axi4_intf.total_errors

        # Log test result
        if total_errors == 0:
            self.log.info(f"Basic write test PASSED - all {total_transactions} transactions had correct split count (1)")
        else:
            self.log.error(f"Basic write test FAILED with {total_errors} errors")

        # Store test results
        self.test_results['test_01_basic_write'] = (total_errors == 0)

        self.log.info(f"Test 01 Basic Write completed with {total_errors} errors")
        return total_errors == 0

    async def test_02_split_test(self):
        """
        Test 02: Split test, checking boundary conditions for splits.

        This test verifies write transactions that cross alignment boundaries
        to ensure proper splitting behavior in different scenarios.
        """
        self.log.info("Starting Test 02: Split Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Get the data width in bytes
        size = self.axi4_intf.dsize
        bytes_per_beat = 1 << size

        # Scale alignment boundaries based on data width
        # The alignment boundary must be at least as large as bytes_per_beat
        # to ensure proper splitting behavior with wider data buses
        if bytes_per_beat <= 8:  # 32-bit or 64-bit
            alignment_masks = [0x07F, 0x0FF, 0x1FF, 0x3FF, 0x7FF, 0xFFF]
        elif bytes_per_beat == 16:  # 128-bit
            alignment_masks = [0x0FF, 0x1FF, 0x3FF, 0x7FF, 0xFFF] 
        elif bytes_per_beat == 32:  # 256-bit
            alignment_masks = [0x1FF, 0x3FF, 0x7FF, 0xFFF]
        else:  # 512-bit
            alignment_masks = [0x3FF, 0x7FF, 0xFFF]
        # alignment_masks = [0x07F]

        # Iterate with various delays
        rand_keys = [
            ('fixed', 'fixed'),
            ('always_ready', 'always_ready'),
            ('fast_ready', 'fast'),
            ('slow_ready', 'slow')
        ]

        # Track total errors
        total_errors = 0

        # Size is fixed based on the interface
        size = self.axi4_intf.dsize
        bytes_per_beat = 1 << size

        # Maximum ID value (for masking)
        max_id = (1 << self.id_width) - 1  # Typically 255 for 8-bit ID

        # For each alignment mask
        for alignment_index, alignment_mask in enumerate(alignment_masks):
            self.log.info(f"Testing alignment mask: 0x{alignment_mask:X}")

            # Set the alignment mask in the DUT
            self.axi4_intf.set_dut_alignment_mask(alignment_mask)

            # For each timing configuration
            for timing_index, (split_rand, axi_rand) in enumerate(rand_keys):
                # Set timing modes
                self.fub_intf.set_split_readiness(split_rand)
                self.fub_intf.set_error_readiness(split_rand)
                self.axi4_intf.set_fub_aw_timing(axi_rand)
                self.axi4_intf.set_fub_w_timing(axi_rand)
                self.axi4_intf.set_m_axi_b_timing(axi_rand)

                # Base address for this set of tests - make sure it's aligned
                base_addr_sector = 0x10000 + (alignment_index * 0x10000) + (timing_index * 0x1000)

                # Let's create a proper boundary-aligned address
                boundary_size = alignment_mask + 1  # e.g., 0x7F -> 0x80, 0xFF -> 0x100
                boundary_addr = ((base_addr_sector + boundary_size) // boundary_size) * boundary_size

                # Case 1: End burst exactly at the boundary
                beats_before_boundary = 4
                case1_addr = boundary_addr - (bytes_per_beat * beats_before_boundary)
                case1_addr = case1_addr & ~(bytes_per_beat - 1)  # Ensure alignment
                case1_length = beats_before_boundary - 1  # Will end right at boundary

                # Generate test data
                case1_data = [(case1_addr + 0xA0000000 + (0x1000 * beat)) & 0xFFFFFFFF for beat in range(case1_length + 1)]

                # Generate ID and mask it to max value
                id_value = (alignment_index * 10 + timing_index * 3 + 1) & max_id

                # Calculate where last byte will be
                last_byte_addr = case1_addr + (bytes_per_beat * (case1_length + 1)) - 1

                # Check if split will happen
                start_segment = case1_addr // boundary_size
                end_segment = last_byte_addr // boundary_size
                expected_splits = 1 + (end_segment - start_segment)

                # Log details for debugging
                self.log.info(f"Test02: Case 1: addr=0x{case1_addr:X}, length={case1_length}, last_byte=0x{last_byte_addr:X}")
                self.log.info(f"Test02:        boundary=0x{boundary_addr:X}, expected_splits={expected_splits}, id=0x{id_value:X}")

                # Register expected transaction
                self.fub_intf.expect_split(id_value, expected_splits)

                # Send write request
                await self.axi4_intf.send_write(case1_addr, case1_data, case1_length, id_value=id_value)

                # Brief delay
                await self.wait_clocks('aclk', 20)

                # Case 2: Start before boundary, cross into next region
                case2_addr = boundary_addr - (bytes_per_beat * 2)
                case2_addr = case2_addr & ~(bytes_per_beat - 1)  # Ensure alignment
                case2_length = 4  # Cross boundary with 5 beats total

                # Generate test data
                case2_data = [(case2_addr + 0xA0000000 + (0x1000 * beat)) & 0xFFFFFFFF for beat in range(case2_length + 1)]

                # Generate ID and mask it to max value
                id_value = (alignment_index * 10 + timing_index * 3 + 2) & max_id

                # Calculate where last byte will be
                last_byte_addr = case2_addr + (bytes_per_beat * (case2_length + 1)) - 1

                # Check if split will happen
                start_segment = case2_addr // boundary_size
                end_segment = last_byte_addr // boundary_size
                expected_splits = 1 + (end_segment - start_segment)

                # Log details for debugging
                self.log.info(f"Test02: Case 2: addr=0x{case2_addr:X}, length={case2_length}, last_byte=0x{last_byte_addr:X}")
                self.log.info(f"Test02:        boundary=0x{boundary_addr:X}, expected_splits={expected_splits}, id=0x{id_value:X}")

                # Register expected transaction
                self.fub_intf.expect_split(id_value, expected_splits)

                # Send write request
                await self.axi4_intf.send_write(case2_addr, case2_data, case2_length, id_value=id_value)

                # Brief delay
                await self.wait_clocks('aclk', 20)

                # Case 3: Multiple splits - start right before boundary
                case3_addr = boundary_addr - bytes_per_beat
                case3_addr = case3_addr & ~(bytes_per_beat - 1)  # Ensure alignment
                case3_length = 15  # Maximum AXI4 burst (16 beats)

                # Generate test data
                case3_data = [(case3_addr + 0xA0000000 + (0x1000 * beat)) & 0xFFFFFFFF for beat in range(case3_length + 1)]

                # Generate ID and mask it to max value
                id_value = (alignment_index * 10 + timing_index * 3 + 3) & max_id

                # Calculate where last byte will be
                last_byte_addr = case3_addr + (bytes_per_beat * (case3_length + 1)) - 1

                # Check if split will happen
                start_segment = case3_addr // boundary_size
                end_segment = last_byte_addr // boundary_size
                expected_splits = 1 + (end_segment - start_segment)

                # Log details for debugging
                self.log.info(f"Test02: Case 3: addr=0x{case3_addr:X}, length={case3_length}, last_byte=0x{last_byte_addr:X}")
                self.log.info(f"Test02:       boundary=0x{boundary_addr:X}, expected_splits={expected_splits}, id=0x{id_value:X}")

                # Register expected transaction
                self.fub_intf.expect_split(id_value, expected_splits)

                # Send write request
                await self.axi4_intf.send_write(case3_addr, case3_data, case3_length, id_value=id_value)

                # Longer delay after case 3 to ensure completion
                await self.wait_clocks('aclk', 50)

        # Wait for all transactions to complete
        self.log.info("Waiting for all transactions to complete...")
        await self.wait_clocks('aclk', 100)  # Fixed delay for simplicity

        # Verify split information
        timeout_ns = 100000
        await self.fub_intf.wait_for_splits(3, timeout_ns)  # We sent 3 transactions per config

        # Add errors from interfaces
        total_errors += self.fub_intf.total_errors + self.axi4_intf.total_errors

        # Store test results
        self.test_results['test_02_split_test'] = (total_errors == 0)

        self.log.info(f"Test 02 Split Test completed with {total_errors} errors")
        return total_errors == 0

    async def test_03_response_error_test(self):
        """
        Test 03: Response Error Test, test error responses.

        Tests error responses for various split and no split cases
        and ensures they show up correctly on the error interface.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 03: Response Error Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Set fast timing for clean test
        self.fub_intf.set_split_readiness('fast_ready')
        self.fub_intf.set_error_readiness('fast_ready')
        self.axi4_intf.set_fub_aw_timing('fast')
        self.axi4_intf.set_fub_w_timing('fast')
        self.axi4_intf.set_m_axi_b_timing('fast')

        # Enable response error injection
        self.axi4_intf.configure_error_injection('resp', True, 1.0)  # Always inject errors
        await self.axi4_intf.start_error_injection()

        # Test cases with different alignment boundaries and split conditions
        test_cases = []

        # No split case (large boundary)
        test_cases.append((4096, 64, 0, 2, 1, f"No split response error"))

        # Single split case
        test_cases.append((256, 224, 2, 2, 2, f"Single split response error"))

        # Multiple split case
        test_cases.append((256, 224, 15, 2, 3, f"Multiple split response error"))

        total_errors = 0
        total_transactions = 0

        for alignment_mask, addr, length, size, expected_splits, description in test_cases:
            total_transactions += 1
            self.log.info(f"Running response error test: {description}")

            # Set alignment mask
            self.axi4_intf.set_dut_alignment_mask(alignment_mask)

            # Register expected error (SLVERR or DECERR)
            id_value = total_transactions
            self.fub_intf.expect_error(id_value, ErrorType.B_RESP_ERROR)

            # Register expected split
            self.fub_intf.expect_split(id_value, expected_splits)

            # Generate test data
            test_data = [(addr + 0xA0000000 + (0x1000 * beat)) & 0xFFFFFFFF for beat in range(length + 1)]

            # Send write request
            await self.axi4_intf.send_write(addr, test_data, length, id_value=id_value)

            # Brief delay between transactions
            await self.wait_clocks('aclk', 100)

        # Wait for all transactions to complete and errors to be reported
        self.log.info("Waiting for all errors to be reported...")
        await self.wait_clocks('aclk', total_transactions * 200)

        # Verify error information
        self.log.info(f"Waiting for error reports...")
        await self.fub_intf.wait_for_errors(total_transactions, 100000)

        # Verify right number of errors were detected
        error_count = self.fub_intf.get_error_count(ErrorType.B_RESP_ERROR)
        if error_count != total_transactions:
            self.log.error(f"Error count mismatch: expected={total_transactions}, actual={error_count}")
            total_errors += 1

        # Add errors from interfaces
        total_errors += self.fub_intf.total_errors + self.axi4_intf.total_errors

        # Store test results
        self.test_results['test_03_response_error_test'] = (total_errors == 0)

        self.log.info(f"Test 03 Response Error Test completed with {total_errors} errors")
        return total_errors == 0

    async def test_04_aw_timeout_test(self):
        """
        Test 04: AW Timeout Test, test AW channel timeout detection.

        Issues a write on the fub_aw channel, but delays acceptance on the m_axi_aw channel to trigger timeout.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 04: AW Timeout Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Set fast timing for W channel and B channel, but slow for AW channel
        self.fub_intf.set_split_readiness('fast_ready')
        self.fub_intf.set_error_readiness('fast_ready')
        self.axi4_intf.set_fub_w_timing('fast')
        self.axi4_intf.set_m_axi_b_timing('fast')

        # Generate timeout values to test around the configured timeout
        timeout_values = generate_timeout_test_values(self.timeout_aw, 6)  # 6 test points

        total_errors = 0
        total_transactions = 0
        expected_timeouts = 0

        # Run tests with different timeout delays
        for aw_timeout in timeout_values:
            total_transactions += 1

            # Create custom randomizer for this specific timeout
            if aw_timeout >= self.timeout_aw:
                # Should timeout
                expected_timeouts += 1
                self.fub_intf.expect_error(total_transactions, ErrorType.AW_TIMEOUT)

                # Configure for AR timeout
                self.axi4_intf.configure_error_injection('aw_timeout', True, 1.0)
                self.log.info(f"Testing AW timeout: {aw_timeout} clocks (should timeout)")
            else:
                # Should not timeout
                self.axi4_intf.configure_error_injection('aw_timeout', False)
                self.log.info(f"Testing AW timeout: {aw_timeout} clocks (should not timeout)")

            # Start error injection
            await self.axi4_intf.start_error_injection()

            # Large alignment mask to avoid splits
            self.axi4_intf.set_dut_alignment_mask(1 << 20)

            # Send single-beat write transaction
            addr = 64 * total_transactions
            data = [0xAAAA0000 + addr]
            length = 0  # 1 beat

            # Send write request
            await self.axi4_intf.send_write(addr, data, length, id_value=total_transactions)

            # Adequate delay for timeout to trigger or not
            await self.wait_clocks('aclk', aw_timeout * 2)

            # Disable error injection before next test
            self.axi4_intf.configure_error_injection('aw_timeout', False)

        # Wait for all transactions to complete or timeout
        self.log.info("Waiting for all transactions to complete or timeout...")
        await self.wait_clocks('aclk', total_transactions * self.timeout_aw * 3)

        # Verify AW timeout errors were reported
        self.log.info(f"Waiting for error reports...")
        await self.fub_intf.wait_for_errors(expected_timeouts, 100000)

        # Verify right number of AW timeouts were detected
        aw_timeout_count = self.fub_intf.get_error_count(ErrorType.AW_TIMEOUT)
        if aw_timeout_count != expected_timeouts:
            self.log.error(f"AW timeout count mismatch: expected={expected_timeouts}, actual={aw_timeout_count}")
            total_errors += 1

        # Add errors from interfaces
        total_errors += self.fub_intf.total_errors + self.axi4_intf.total_errors

        # Store test results
        self.test_results['test_04_aw_timeout_test'] = (total_errors == 0)

        self.log.info(f"Test 04 AW Timeout Test completed with {total_errors} errors")
        return total_errors == 0

    async def test_05_w_timeout_test(self):
        """
        Test 05: W Timeout Test, test W channel timeout detection.

        Issues a write with AW accepted but W channel timeout.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 05: W Timeout Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Set fast timing for AW channel and B channel, but slow for W channel
        self.fub_intf.set_split_readiness('fast_ready')
        self.fub_intf.set_error_readiness('fast_ready')
        self.axi4_intf.set_fub_aw_timing('fast')
        self.axi4_intf.set_m_axi_b_timing('fast')

        # Generate timeout values to test around the configured timeout
        timeout_values = generate_timeout_test_values(self.timeout_w, 6)  # 6 test points

        total_errors = 0
        total_transactions = 0
        expected_timeouts = 0

        # Run tests with different timeout delays
        for w_timeout in timeout_values:
            total_transactions += 1

            # Configure for this specific timeout
            if w_timeout >= self.timeout_w:
                # Should timeout
                expected_timeouts += 1
                self.fub_intf.expect_error(total_transactions, ErrorType.W_TIMEOUT)

                # Configure for W timeout
                self.axi4_intf.configure_error_injection('w_timeout', True, 1.0)
                self.log.info(f"Testing W timeout: {w_timeout} clocks (should timeout)")
            else:
                # Should not timeout
                self.axi4_intf.configure_error_injection('w_timeout', False)
                self.log.info(f"Testing W timeout: {w_timeout} clocks (should not timeout)")

            # Start error injection
            await self.axi4_intf.start_error_injection()

            # Large alignment mask to avoid splits
            self.axi4_intf.set_dut_alignment_mask(1 << 20)

            # Send write transaction with multiple beats to ensure W channel timeouts
            addr = 64 * total_transactions
            data = [0xAAAA0000 + addr + (0x1000 * i) for i in range(4)]
            length = 3  # 4 beats

            # Send write request
            await self.axi4_intf.send_write(addr, data, length, id_value=total_transactions)

            # Adequate delay for timeout to trigger or not
            await self.wait_clocks('aclk', w_timeout * 2)

            # Disable error injection before next test
            self.axi4_intf.configure_error_injection('w_timeout', False)

        # Wait for all transactions to complete or timeout
        self.log.info("Waiting for all transactions to complete or timeout...")
        await self.wait_clocks('aclk', total_transactions * self.timeout_w * 3)

        # Verify W timeout errors were reported
        self.log.info(f"Waiting for error reports...")
        await self.fub_intf.wait_for_errors(expected_timeouts, 100000)

        # Verify right number of W timeouts were detected
        w_timeout_count = self.fub_intf.get_error_count(ErrorType.W_TIMEOUT)
        if w_timeout_count != expected_timeouts:
            self.log.error(f"W timeout count mismatch: expected={expected_timeouts}, actual={w_timeout_count}")
            total_errors += 1

        # Add errors from interfaces
        total_errors += self.fub_intf.total_errors + self.axi4_intf.total_errors

        # Store test results
        self.test_results['test_05_w_timeout_test'] = (total_errors == 0)

        self.log.info(f"Test 05 W Timeout Test completed with {total_errors} errors")
        return total_errors == 0

    async def test_06_b_timeout_test(self):
        """
        Test 06: B Timeout Test, test B channel timeout detection.

        Issues a write with AW and W channels accepted but B channel timeout.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 06: B Timeout Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Set fast timing for AW and W channels, but slow for B channel
        self.fub_intf.set_split_readiness('fast_ready')
        self.fub_intf.set_error_readiness('fast_ready')
        self.axi4_intf.set_fub_aw_timing('fast')
        self.axi4_intf.set_fub_w_timing('fast')

        # Generate timeout values to test around the configured timeout
        timeout_values = generate_timeout_test_values(self.timeout_b, 6)  # 6 test points

        total_errors = 0
        total_transactions = 0
        expected_timeouts = 0

        # Run tests with different timeout delays
        for b_timeout in timeout_values:
            total_transactions += 1

            # Configure for this specific timeout
            if b_timeout >= self.timeout_b:
                # Should timeout
                expected_timeouts += 1
                self.fub_intf.expect_error(total_transactions, ErrorType.B_TIMEOUT)

                # Set timing to trigger timeout
                self.axi4_intf.set_m_axi_b_timing('timeout')
                self.log.info(f"Testing B timeout: {b_timeout} clocks (should timeout)")
            else:
                # Should not timeout
                self.axi4_intf.set_m_axi_b_timing('slow')
                self.log.info(f"Testing B timeout: {b_timeout} clocks (should not timeout)")

            # Large alignment mask to avoid splits
            self.axi4_intf.set_dut_alignment_mask(1 << 20)

            # Send single-beat write transaction
            addr = 64 * total_transactions
            data = [0xAAAA0000 + addr]
            length = 0  # 1 beat

            # Send write request
            await self.axi4_intf.send_write(addr, data, length, id_value=total_transactions)

            # Adequate delay for timeout to trigger or not
            await self.wait_clocks('aclk', b_timeout * 2)

        # Wait for all transactions to complete or timeout
        self.log.info("Waiting for all transactions to complete or timeout...")
        await self.wait_clocks('aclk', total_transactions * self.timeout_b * 3)

        # Verify B timeout errors were reported
        self.log.info(f"Waiting for error reports...")
        await self.fub_intf.wait_for_errors(expected_timeouts, 100000)

        # Verify right number of B timeouts were detected
        b_timeout_count = self.fub_intf.get_error_count(ErrorType.B_TIMEOUT)
        if b_timeout_count != expected_timeouts:
            self.log.error(f"B timeout count mismatch: expected={expected_timeouts}, actual={b_timeout_count}")
            total_errors += 1

        # Add errors from interfaces
        total_errors += self.fub_intf.total_errors + self.axi4_intf.total_errors

        # Store test results
        self.test_results['test_06_b_timeout_test'] = (total_errors == 0)

        self.log.info(f"Test 06 B Timeout Test completed with {total_errors} errors")
        return total_errors == 0

    async def test_07_collision_cases(self):
        """
        Test 07: Collision cases, test error collision reporting.

        Try to collide Response Error/WT/AWT/BTO to test that
        even if 2-3 of them happen at once, they all get reported.

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("Starting Test 07: Collision Cases Test")

        # Reset the DUT and interfaces
        await self.reset_dut()

        # Set fast readiness for error reporting
        self.fub_intf.set_split_readiness('fast_ready')
        self.fub_intf.set_error_readiness('fast_ready')

        # Create test matrix for error collisions
        collision_matrix = create_collision_test_matrix()

        total_errors = 0
        total_cases = 0

        # Run each collision test case
        for error_types in collision_matrix:
            total_cases += 1
            self.log.info(f"Testing error collision: {[ErrorType(et).name for et in error_types]}")

            # Configure error injection for this case
            self.axi4_intf.configure_error_injection('resp', ErrorType.B_RESP_ERROR in error_types, 1.0)
            self.axi4_intf.configure_error_injection('aw_timeout', ErrorType.AW_TIMEOUT in error_types, 1.0)
            self.axi4_intf.configure_error_injection('w_timeout', ErrorType.W_TIMEOUT in error_types, 1.0)
            self.axi4_intf.configure_error_injection('b_timeout', ErrorType.B_TIMEOUT in error_types, 1.0)

            # Start error injection
            await self.axi4_intf.start_error_injection()

            # For each error type, expect it to be reported
            for error_type in error_types:
                self.fub_intf.expect_error(total_cases, error_type)

            # Send write transaction
            addr = 64 * total_cases
            data = [0xAAAA0000 + addr]
            length = 0  # 1 beat

            # Send write request
            await self.axi4_intf.send_write(addr, data, length, id_value=total_cases)

            # Wait for errors to be reported
            self.log.info("Waiting for collision errors to be reported...")
            await self.wait_clocks('aclk', 1000)

            # Verify that the expected error types were detected
            success = await self.fub_intf.verify_collision_behavior(error_types, 2000)
            if not success:
                self.log.error(f"Collision test failed for types: {[ErrorType(et).name for et in error_types]}")
                total_errors += 1

            # Disable error injection before next test
            self.axi4_intf.configure_error_injection('resp', False)
            self.axi4_intf.configure_error_injection('aw_timeout', False)
            self.axi4_intf.configure_error_injection('w_timeout', False)
            self.axi4_intf.configure_error_injection('b_timeout', False)

            # Delay between cases
            await self.wait_clocks('aclk', 1000)

        # Add errors from interfaces
        total_errors += self.fub_intf.total_errors + self.axi4_intf.total_errors

        # Store test results
        self.test_results['test_07_collision_cases'] = (total_errors == 0)

        self.log.info(f"Test 07 Collision Cases completed with {total_errors} errors")
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
