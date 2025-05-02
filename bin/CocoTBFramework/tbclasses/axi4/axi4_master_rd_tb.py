from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.axi4.axi4_factory import create_axi4_master, create_axi4_slave
from CocoTBFramework.tbclasses.axi4.axi4_fub_error_slave import AXIErrorMonitorSlave
from CocoTBFramework.tbclasses.axi4.axi4_fub_split_slave import AXISplitMonitorSlave
from CocoTBFramework.components.axi4.axi4_seq_transaction import AXI4TransactionSequence
from CocoTBFramework.tbclasses.axi4.axi4_random_configs import RANDOMIZER_CONFIGS


class AXI4MasterReadTB(TBBase):
    """
    Testbench for AXI4 Master Read module with split tracking and error monitoring
    """

    def __init__(self, dut,
                    id_width=8,
                    addr_width=32,
                    data_width=32,
                    user_width=1,
                    alignment_mask=0xFFF,
                    channels=32,
                    skid_depth_ar=2,
                    skid_depth_r=4,
                    timeout_ar=32,
                    timeout_r=32,
                    error_fifo_depth=4,
                    split_fifo_depth=4):
        """
        Initialize the testbench with the DUT and configuration parameters
        """
        super().__init__(dut)

        # Store configuration parameters
        self.id_width = id_width
        self.addr_width = addr_width
        self.data_width = data_width
        self.user_width = user_width
        self.alignment_mask = alignment_mask
        self.strb_width = data_width // 8
        self.memory_size = 32768  # Size in lines
        self.channels = channels
        self.error_fifo_depth = error_fifo_depth
        self.timeout_ar = timeout_ar
        self.timeout_r = timeout_r

        # Create memory model for AXI slave
        self.mem = MemoryModel(
            num_lines=self.memory_size,
            bytes_per_line=self.strb_width,
            log=self.log
        )

        # Create randomizers for timing control - these will be applied to individual channels
        self.fub_randomizer = FlexRandomizer(RANDOMIZER_CONFIGS['constrained']['write'])
        self.axi_randomizer = FlexRandomizer(RANDOMIZER_CONFIGS['constrained']['read'])

        # Set initial alignment mask register
        dut.alignment_mask.value = alignment_mask

        # Setup tracking for transactions, errors, and splits
        self.transactions = {}
        self.error_reports = []
        self.split_reports = []

        # Initialize components to None
        self.fub_master = None
        self.axi_slave = None
        self.error_monitor_slave = None
        self.split_monitor_slave = None

        # Initialize test results
        self.total_errors = 0

        # Log the configuration
        self._log_config()

    def _log_config(self):  # sourcery skip: class-extract-method
        """Log the testbench configuration"""
        self.log.info("=" * 80)
        self.log.info("AXI4 Master Read Testbench Configuration:")
        self.log.info("-" * 80)
        self.log.info(f"ID Width:       {self.id_width}")
        self.log.info(f"Address Width:  {self.addr_width}")
        self.log.info(f"Data Width:     {self.data_width}")
        self.log.info(f"User Width:     {self.user_width}")
        self.log.info(f"Alignment Mask: 0x{self.alignment_mask:X}")
        self.log.info("=" * 80)

    async def setup_components(self):
        """Create and initialize all BFM components"""
        self.log.info("Setting up testbench components")

        # Create AXI4 Master for the FUB side (input)
        self.fub_master = create_axi4_master(
            dut=self.dut,
            title="fub_master",
            prefix="fub",
            divider="",
            suffix="",
            clock=self.dut.aclk,
            channels=["AR", "R"],  # Read channels only
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width,
            log=self.log
        )

        # Set randomizers for individual channels
        self.fub_master.ar_master.set_randomizer(self.fub_randomizer)
        self.fub_master.r_slave.set_randomizer(self.fub_randomizer)

        # Create AXI4 Slave for the AXI4 side (output)
        self.axi_slave = create_axi4_slave(
            dut=self.dut,
            title="axi_slave",
            prefix="m_axi",
            divider="",
            suffix="",
            clock=self.dut.aclk,
            channels=["AR", "R"],  # Read channels only
            memory_model=self.mem,
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width,
            log=self.log
        )

        # Set randomizers for individual channels
        self.axi_slave.ar_slave.set_randomizer(self.axi_randomizer)
        self.axi_slave.r_master.set_randomizer(self.axi_randomizer)

        # Create Error Monitor/Slave for the error FIFO interface
        self.error_monitor_slave = AXIErrorMonitorSlave(
            dut=self.dut,
            clock=self.dut.aclk,
            axi_addr_width=self.addr_width,
            axi_id_width=self.id_width,
            title_prefix="Error",
            randomizer=self.fub_randomizer,
            log=self.log
        )

        # Create Split Monitor/Slave for the split FIFO interface
        self.split_monitor_slave = AXISplitMonitorSlave(
            dut=self.dut,
            clock=self.dut.aclk,
            axi_addr_width=self.addr_width,
            axi_id_width=self.id_width,
            title_prefix="Split",
            randomizer=self.fub_randomizer,
            log=self.log
        )

        # Register callbacks for monitoring
        self.error_monitor_slave.add_error_callback(self._on_error_report)
        self.split_monitor_slave.add_split_callback(self._on_split_report)

        # Initialize memory with a test pattern
        await self._initialize_memory()

        self.log.info("Components setup complete")

    def _on_error_report(self, transaction):
        """Callback for error reports"""
        error_type = transaction.error_type
        error_id = transaction.error_id
        error_addr = transaction.error_addr

        error_type_str = ""
        if error_type & 0x1:
            error_type_str += "AR_TIMEOUT "
        if error_type & 0x2:
            error_type_str += "R_TIMEOUT "
        if error_type & 0x8:
            error_type_str += "RESP_ERROR "

        error_info = {
            'type': error_type,
            'type_str': error_type_str.strip(),
            'id': error_id,
            'addr': error_addr
        }

        self.log.info(f"Error detected: {error_info['type_str']} for ID={error_id}, addr=0x{error_addr:X}")
        self.error_reports.append(error_info)

    def _on_split_report(self, transaction):
        """Callback for split reports"""
        split_addr = transaction.split_addr
        split_id = transaction.split_id
        split_cnt = transaction.split_cnt

        split_info = {
            'addr': split_addr,
            'id': split_id,
            'count': split_cnt
        }

        self.log.info(f"Split detected: ID={split_id}, addr=0x{split_addr:X}, count={split_cnt}")
        self.split_reports.append(split_info)

    async def _initialize_memory(self):
        """Initialize memory with a test pattern"""
        # Use a pattern: address + 0xA5A5A5A5
        for addr in range(0, self.memory_size * self.strb_width, self.strb_width):
            value = (addr + 0xA5A5A5A5) & ((1 << (8 * self.strb_width)) - 1)
            data_bytes = self.mem.integer_to_bytearray(value, self.strb_width)
            self.mem.write(addr, data_bytes, 0xFF)  # All bytes enabled

        # Add some special patterns at key locations for testing
        # Pattern at 4K boundary - used for testing splits
        boundary_addr = 0x1000  # 4K boundary
        for i in range(16):
            addr = boundary_addr - self.strb_width * 8 + i * self.strb_width
            value = 0xB0000000 + i
            data_bytes = self.mem.integer_to_bytearray(value, self.strb_width)
            self.mem.write(addr, data_bytes, 0xFF)

            addr = boundary_addr + i * self.strb_width
            value = 0xC0000000 + i
            data_bytes = self.mem.integer_to_bytearray(value, self.strb_width)
            self.mem.write(addr, data_bytes, 0xFF)

        self.log.info("Memory initialized with test patterns")

    async def set_alignment_mask(self, mask):
        """Set the alignment mask register"""
        self.dut.alignment_mask.value = mask
        self.alignment_mask = mask
        self.log.info(f"Alignment mask set to 0x{mask:X}")
        # Wait a clock cycle for the value to propagate
        await self.wait_clocks('aclk', 1)

    async def reset_dut(self):
        """Reset the DUT and components"""
        self.log.info("Resetting DUT and components")

        # Reset the DUT
        self.dut.aresetn.value = 0

        # Reset the BFM components
        if self.fub_master:
            await self.fub_master.reset_bus()
        if self.axi_slave:
            await self.axi_slave.reset_bus()
        if self.error_monitor_slave:
            await self.error_monitor_slave.reset_bus()
        if self.split_monitor_slave:
            await self.split_monitor_slave.reset_bus()

        # Wait for reset to stabilize
        await self.wait_clocks('aclk', 5)

        # Remove reset
        self.dut.aresetn.value = 1

        # Wait for components to initialize
        await self.wait_clocks('aclk', 5)

        # Clear all tracking data
        self.transactions = {}
        self.error_reports = []
        self.split_reports = []

        self.log.info("Reset complete")

    async def start_components(self):
        """Start all active components"""
        self.log.info("Starting components")

        # Start AXI slave processor
        await self.axi_slave.start_processor()

        self.log.info("Components started")

    async def stop_components(self):
        """Stop all active components"""
        self.log.info("Stopping components")

        # Stop AXI slave processor
        await self.axi_slave.stop_processor()

        self.log.info("Components stopped")

    def calculate_expected_splits(self, addr, burst_len, burst_size):
        """
        Calculate expected number of splits based on current alignment mask

        Args:
            addr: Starting address
            burst_len: Burst length (0 = 1 beat, N = N+1 beats)
            burst_size: Size (log2 of bytes)

        Returns:
            Expected number of splits
        """
        bytes_per_transfer = 1 << burst_size
        total_bytes = (burst_len + 1) * bytes_per_transfer
        end_addr = addr + total_bytes - 1

        # Calculate boundaries crossed using current alignment mask
        start_boundary = addr & ~self.alignment_mask
        end_boundary = end_addr & ~self.alignment_mask

        # If all data fits within a single boundary region, no split needed
        if start_boundary == end_boundary:
            return 1

        # Calculate how many boundaries are crossed
        boundary_size = self.alignment_mask + 1
        return ((end_boundary - start_boundary) // boundary_size) + 1

    async def perform_read(self, addr, id_value=0, burst_len=0, burst_size=None):
        """
        Perform a read transaction with the given parameters

        Args:
            addr: Address to read from
            id_value: AXI ID for the transaction
            burst_len: Burst length (0 = single beat, N = N+1 beats)
            burst_size: Size (log2 of bytes), defaults to max for data width

        Returns:
            The result dictionary from the read operation
        """
        # If burst_size not specified, use max for data width
        if burst_size is None:
            burst_size = (self.data_width // 8).bit_length() - 1

        # Burst type is always INCR for this DUT
        burst_type = 1  # INCR

        # Track this transaction
        txn_key = f"{id_value:X}_{addr:X}"
        self.transactions[txn_key] = {
            'addr': addr,
            'id': id_value,
            'burst_len': burst_len,
            'burst_size': burst_size,
            'status': 'STARTED',
            'response': None,
            'splits': [],
            'errors': []
        }

        self.log.info(f"Performing read: addr=0x{addr:X}, id={id_value}, burst_len={burst_len}, burst_size={burst_size}")

        # Perform the read
        result = await self.fub_master.read(
            addr=addr,
            id=id_value,
            burst=burst_type,  # INCR
            length=burst_len,
            size=burst_size
        )

        # Update transaction status
        self.transactions[txn_key]['status'] = 'COMPLETED'
        self.transactions[txn_key]['response'] = result

        # Check for associated errors and splits
        for error in self.error_reports:
            if error['id'] == id_value:
                self.transactions[txn_key]['errors'].append(error)

        for split in self.split_reports:
            if split['id'] == id_value and split['addr'] == addr:
                self.transactions[txn_key]['splits'].append(split)

        return result

    async def verify_read_data(self, result, addr, burst_len=0, burst_size=None):
        """
        Verify the read data against expected values in memory

        Args:
            result: Result from read operation
            addr: Address read from
            burst_len: Burst length used
            burst_size: Size (log2 of bytes) used

        Returns:
            True if data matches expected, False otherwise
        """
        # If burst_size not specified, use max for data width
        if burst_size is None:
            burst_size = (self.data_width // 8).bit_length() - 1

        # Calculate bytes per transfer
        bytes_per_transfer = 1 << burst_size

        # Create appropriate mask based on transfer size
        size_mask = (1 << (8 * bytes_per_transfer)) - 1

        # Check each beat
        all_match = True
        for i, read_value in enumerate(result['data']):
            # Calculate address for this beat (INCR)
            current_addr = addr + i * bytes_per_transfer

            # Read expected value from memory
            expected_bytes = self.mem.read(current_addr, bytes_per_transfer)
            expected_value = self.mem.bytearray_to_integer(expected_bytes)

            # For smaller transfer sizes, we need to extract the correct bytes
            # The data alignment depends on the address
            byte_offset = current_addr % self.strb_width
            bit_offset = byte_offset * 8

            # For transfers smaller than full data width, extract the appropriate bytes
            if bytes_per_transfer < self.strb_width:
                # Extract the relevant bytes based on size and address alignment
                masked_expected = (expected_value >> bit_offset) & size_mask
                masked_read = (read_value >> bit_offset) & size_mask
            else:
                # For full-width transfers, use the entire value
                masked_expected = expected_value
                masked_read = read_value

            # Compare
            if masked_read != masked_expected:
                self.log.error(f"Data mismatch at beat {i}, addr=0x{current_addr:X}: "
                            f"expected=0x{masked_expected:X}, got=0x{masked_read:X}")
                all_match = False
                self.total_errors += 1
            else:
                self.log.debug(f"Data match at beat {i}, addr=0x{current_addr:X}: "
                            f"value=0x{masked_read:X}")

        return all_match

    async def verify_split_transaction(self, result, addr, id_value, burst_len, burst_size, expected_splits):
        """
        Verify that transaction was split correctly

        Args:
            result: Result from read operation
            addr: Address read from
            id_value: Transaction ID
            burst_len: Burst length used
            burst_size: Size (log2 of bytes) used
            expected_splits: Expected number of splits

        Returns:
            True if transaction was split as expected, False otherwise
        """
        # Find transaction info
        txn_key = f"{id_value:X}_{addr:X}"
        txn_info = self.transactions.get(txn_key, None)

        if not txn_info:
            self.log.error(f"Transaction info not found for addr=0x{addr:X}, id={id_value}")
            self.total_errors += 1
            return False

        # Wait for split information to arrive - add a timeout to prevent hanging
        max_wait_cycles = 100
        wait_count = 0

        while wait_count < max_wait_cycles:
            # Check if we have any split reports for this transaction
            splits = txn_info.get('splits', [])

            if len(splits) > 0:
                # Split info has arrived
                break

            # Wait a few clock cycles for FIFO processing
            await self.wait_clocks('aclk', 5)
            wait_count += 5

            # Refresh the transaction info from our tracking dictionary
            txn_info = self.transactions.get(txn_key, None)

            # Check for any new split reports
            for split in self.split_reports:
                if split['id'] == id_value and split['addr'] == addr and split not in txn_info.get('splits', []):
                    txn_info.setdefault('splits', []).append(split)

        # Now check if we have the expected split information
        splits = txn_info.get('splits', [])

        if len(splits) == 0 and expected_splits > 1:
            self.log.error(f"No splits detected but expected {expected_splits} splits for "
                            f"addr=0x{addr:X}, burst_len={burst_len}, burst_size={burst_size}, "
                            f"alignment_mask=0x{self.alignment_mask:X}")
            self.total_errors += 1
            return False

        # If we have splits, check that count matches expectation
        if splits:
            split_count = splits[0]['count']  # Get the reported split count
            if split_count != expected_splits:
                self.log.error(f"Split count mismatch: expected={expected_splits}, got={split_count} for "
                                f"addr=0x{addr:X}, burst_len={burst_len}, burst_size={burst_size}, "
                                f"alignment_mask=0x{self.alignment_mask:X}")
                self.total_errors += 1
                return False

            self.log.info(f"Transaction correctly split into {split_count} parts")

        # Also verify the data to make sure we got everything despite the split
        data_match = await self.verify_read_data(result, addr, burst_len, burst_size)

        return data_match and (len(splits) == 0 and expected_splits == 1 or
                                len(splits) > 0 and splits[0]['count'] == expected_splits)

    async def configure_slave_response_order(self, inorder=True):
        """
        Configure the AXI slave to respond in-order or out-of-order

        Args:
            inorder: True for in-order responses, False for out-of-order
        """
        # Configure slave response ordering
        self.axi_slave.inorder = inorder

        if not inorder:
            # Set out-of-order strategy to random
            self.axi_slave.ooo_strategy = 'random'
            self.log.info("Slave configured for out-of-order responses")
        else:
            self.log.info("Slave configured for in-order responses")

        # Wait for settings to take effect
        await self.wait_clocks('aclk', 5)

    async def set_pathological_delay(self, interface='fub', channel='valid', timeout_factor=1.5):
        """
        Configure a pathologically large delay to trigger timeouts

        Args:
            interface: 'fub' for FUB side, 'axi' for AXI side
            channel: 'valid' for master valid, 'ready' for slave ready
            timeout_factor: Multiplier for timeout value to ensure timeout occurs
        """
        # Determine appropriate timeout value based on channel
        if channel.lower() == 'valid' and channel.lower() in ['ar', 'w']:
            # Address channel (AR/AW)
            base_timeout = self.timeout_ar
        else:
            # Data channel (R/W/B)
            base_timeout = self.timeout_r

        # Apply factor to ensure delay exceeds timeout
        min_delay = int(base_timeout * timeout_factor)
        max_delay = min_delay + 50  # Add some variability

        delay_config = {
            f'{channel}_delay': ([[min_delay, max_delay]], [1.0])
        }

        patho_randomizer = FlexRandomizer(delay_config)

        if interface.lower() == 'fub':
            if channel.lower() == 'valid':
                self.fub_master.ar_master.set_randomizer(patho_randomizer)
            else:
                self.fub_master.r_slave.set_randomizer(patho_randomizer)
            self.log.info(f"Set pathological {channel} delay on FUB {interface} channel: {min_delay}-{max_delay} cycles")
        else:
            if channel.lower() == 'valid':
                self.axi_slave.r_master.set_randomizer(patho_randomizer)
            else:
                self.axi_slave.ar_slave.set_randomizer(patho_randomizer)
            self.log.info(f"Set pathological {channel} delay on AXI {interface} channel: {min_delay}-{max_delay} cycles")

        # Wait for setting to take effect
        await self.wait_clocks('aclk', 5)

    async def wait_for_timeout_detection(self, timeout_type='ar', additional_margin=20):
        """
        Wait for a sufficient number of cycles for timeout detection

        Args:
            timeout_type: 'ar' for address channel timeout, 'r' for data channel timeout
            additional_margin: Additional cycles to wait beyond the timeout value

        Returns:
            Number of cycles waited
        """
        if timeout_type.lower() == 'ar':
            timeout_cycles = self.timeout_ar
        else:
            timeout_cycles = self.timeout_r

        wait_cycles = timeout_cycles + additional_margin
        self.log.info(f"Waiting {wait_cycles} cycles for {timeout_type.upper()} timeout detection")
        await self.wait_clocks('aclk', wait_cycles)
        return wait_cycles

    def get_test_result(self):
        """Get the test result (True if no errors)"""
        return self.total_errors == 0

    def get_error_count(self):
        """Get the total error count"""
        return self.total_errors

    def get_split_count(self):
        """Get the number of split transactions detected"""
        return len(self.split_reports)

    def get_error_report_count(self):
        """Get the number of error reports detected"""
        return len(self.error_reports)

    def log_summary(self):
        """Log summary of test results"""
        self.log.info("=" * 80)
        self.log.info("Test Summary:")
        self.log.info("-" * 80)
        self.log.info(f"Total transactions: {len(self.transactions)}")
        self.log.info(f"Split transactions: {len(self.split_reports)}")
        self.log.info(f"Error reports:      {len(self.error_reports)}")
        self.log.info(f"Total errors:       {self.total_errors}")

        if self.total_errors == 0:
            self.log.info("TEST PASSED")
        else:
            self.log.error("TEST FAILED")

        self.log.info("=" * 80)

    async def run_transaction_sequence(self, sequence):
        """
        Run a transaction sequence on the DUT

        Args:
            sequence: AXI4TransactionSequence to execute

        Returns:
            True if sequence executed successfully, False otherwise
        """
        self.log.info(f"Running transaction sequence: {sequence.name}")

        # Get all read transactions from the sequence
        read_ids = sequence.get_read_ids()

        # Execute each read transaction
        for read_id in read_ids:
            # Get the read address packet
            ar_packet = sequence.get_read_addr_packet(read_id)
            if not ar_packet:
                continue

            # Extract parameters
            addr = ar_packet.araddr
            burst_len = ar_packet.arlen
            burst_size = ar_packet.arsize

            # Perform the read
            result = await self.perform_read(
                addr=addr,
                id_value=read_id,
                burst_len=burst_len,
                burst_size=burst_size
            )

            if expected_data := sequence.get_read_response_packets(read_id):
                # Verify data if expected response is provided
                expected_values = [packet.rdata for packet in expected_data]

                # Check actual vs expected
                if len(result['data']) != len(expected_values):
                    self.log.error(f"Data length mismatch for ID {read_id}: "
                                    f"expected {len(expected_values)}, got {len(result['data'])}")
                    self.total_errors += 1
                else:
                    for i, (actual, expected) in enumerate(zip(result['data'], expected_values)):
                        if actual != expected:
                            self.log.error(f"Data mismatch at beat {i} for ID {read_id}: "
                                            f"expected=0x{expected:X}, got=0x{actual:X}")
                            self.total_errors += 1
            else:
                # Verify against memory model if no expected data provided
                await self.verify_read_data(result, addr, burst_len, burst_size)

        return self.total_errors == 0

    async def run_boundary_test_sequence(self, masks=None, page_addresses=None):
        """
        Run a boundary test with different alignment masks and page addresses

        Args:
            masks: List of alignment masks to test, defaults to [0xFFF, 0x7FF, 0x3FF]
            page_addresses: List of base page addresses to test, defaults to [0, 0x10000, 0x20000]

        Returns:
            True if all tests passed, False otherwise
        """
        if masks is None:
            masks = [0xFFF, 0x7FF, 0x3FF]  # 4K, 2K, 1K boundaries

        if page_addresses is None:
            page_addresses = [0, 0x10000, 0x20000]  # Default pages to test

        self.log.info("Running boundary test sequence with multiple masks and pages")

        for mask in masks:
            # Set alignment mask
            await self.set_alignment_mask(mask)
            boundary_size = mask + 1

            for base_addr in page_addresses:
                # Create a boundary test sequence for this mask and page
                sequence = AXI4TransactionSequence.create_x_boundary_test(
                    alignment_mask=mask,
                    channel="AR",  # For read tests
                    base_addr=base_addr,
                    data_width=self.data_width
                )

                # Run the sequence
                self.log.info(f"Testing with alignment mask 0x{mask:X}, page address 0x{base_addr:X}")
                success = await self.run_transaction_sequence(sequence)

                if not success:
                    self.log.error(f"Boundary test with mask 0x{mask:X}, page 0x{base_addr:X} failed")
                    return False

                # Wait between tests
                await self.wait_clocks('aclk', 10)

        return True

    async def verify_error_addresses(self, txn_id, expected_addr, error_type=None):
        """
        Verify that error reports have the correct address for a given transaction ID

        Args:
            txn_id: Transaction ID to check errors for
            expected_addr: The expected address for this transaction
            error_type: Optional error type to filter by (bitfield)

        Returns:
            True if all errors for this transaction have the correct address, False otherwise
        """
        # Wait a few cycles for error reporting to complete
        await self.wait_clocks('aclk', 10)

        # Find all errors for this transaction ID
        txn_errors = [err for err in self.error_reports if err['id'] == txn_id]

        # Filter by error type if specified
        if error_type is not None:
            txn_errors = [err for err in txn_errors if err['type'] & error_type]

        # If no errors found but we expect some, that's a failure
        if not txn_errors:
            self.log.error(f"No errors found for ID={txn_id} (expected address 0x{expected_addr:X})")
            self.total_errors += 1
            return False

        # Check addresses for all found errors
        all_match = True
        for err in txn_errors:
            if err['addr'] != expected_addr:
                self.log.error(f"Address mismatch for error type {err['type_str']} "
                            f"with ID={txn_id}: expected=0x{expected_addr:X}, "
                            f"got=0x{err['addr']:X}")
                all_match = False
                self.total_errors += 1
            else:
                self.log.info(f"Address correct for error type {err['type_str']} "
                            f"with ID={txn_id}: addr=0x{err['addr']:X}")

        return all_match

