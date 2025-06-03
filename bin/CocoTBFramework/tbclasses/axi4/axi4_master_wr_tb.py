import random
import cocotb
from cocotb.triggers import Edge
from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.axi4.axi4_seq_protocol import AXI4ProtocolSequence
from CocoTBFramework.components.axi4.axi4_packet import AXI4Packet
from CocoTBFramework.components.axi4.axi4_factory import create_axi4_master, create_axi4_slave
from CocoTBFramework.tbclasses.axi4.axi4_fub_error_slave import AXIErrorMonitorSlave
from CocoTBFramework.tbclasses.axi4.axi4_fub_split_slave import AXISplitMonitorSlave
from CocoTBFramework.components.axi4.axi4_seq_transaction import AXI4TransactionSequence
from CocoTBFramework.tbclasses.axi4.axi4_random_configs import RANDOMIZER_CONFIGS

from CocoTBFramework.tbclasses.common.amba_cg_ctrl import AxiClockGateCtrl

class AXI4MasterWriteTB(TBBase):
    """
    Testbench for AXI4 Master Write module with split tracking and error monitoring
    """

    def __init__(self, dut,
                    id_width=8,
                    addr_width=32,
                    data_width=32,
                    user_width=1,
                    alignment_mask=0xFFF,
                    channels=32,
                    skid_depth_aw=2,
                    skid_depth_w=4,
                    skid_depth_b=2,
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
        self.skid_depth_aw = skid_depth_aw
        self.skid_depth_w = skid_depth_w
        self.skid_depth_b = skid_depth_b
        self.error_fifo_depth = error_fifo_depth

        timeout_addr = 40
        self.timeout_aw = timeout_addr
        self.timeout_w = timeout_addr
        self.timeout_b = timeout_addr * 4

        # set the errmon delay configs
        self.dut.i_cfg_freq_sel.value = 4
        self.dut.i_cfg_addr_cnt.value = 1
        self.dut.i_cfg_data_cnt.value = 4
        self.dut.i_cfg_resp_cnt.value = 6

        # Detect if this DUT has clock gating support
        self.has_clock_gating = hasattr(dut, 'CG_IDLE_COUNT_WIDTH')
        if self.has_clock_gating:
            self.cg_idle_count_width = int(dut.CG_IDLE_COUNT_WIDTH.value)
            self.max_idle_count = (1 << self.cg_idle_count_width) - 1
            self.log.info(f"Clock gating detected with idle count width: {self.cg_idle_count_width}")

            # Create the clock gating controller
            self.cg_ctrl = AxiClockGateCtrl(
                dut,
                instance_path="i_amba_clock_gate_ctrl",  # Path to the instance
                clock_signal_name="clk_in",              # Name of the clock signal
                user_valid_signals=["i_user_valid"],     # User-side valid signals
                axi_valid_signals=["i_axi_valid"]        # AXI-side valid signals
            )

            # Get block_ready signal from the right hierarchy
            if hasattr(dut, 'i_axi_master_wr') and hasattr(dut.i_axi_master_wr, 'int_block_ready'):
                self.block_ready = dut.i_axi_master_wr.int_block_ready
                self.log.info("Using hierarchical path for int_block_ready signal")
            else:
                # Fallback to direct access
                self.block_ready = None
                self.log.warning("Could not find i_axi_master_wr.int_block_ready signal")
        else:
            self.log.info("DUT does not have clock gating support")

            # For non-clock gating case, block_ready is directly accessible
            if hasattr(dut, 'int_block_ready'):
                self.block_ready = dut.int_block_ready
                self.log.info("Using direct path for int_block_ready signal")
            else:
                self.block_ready = None
                self.log.warning("Could not find int_block_ready signal")

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

    # Add these new methods for clock gating control and testing

    def has_cg_support(self):
        """Check if the DUT has clock gating support"""
        return self.has_clock_gating

    async def configure_clock_gating(self, enable=True, idle_count=8):
        """
        Configure clock gating parameters

        Args:
            enable: True to enable clock gating, False to disable
            idle_count: Number of idle cycles before clock gating activates (clamped to max)
        """
        if not self.has_clock_gating:
            self.log.warning("Attempting to configure clock gating on a DUT without support")
            return False

        # Clamp idle count to the maximum supported by the hardware
        if idle_count > self.max_idle_count:
            self.log.warning(f"Idle count {idle_count} exceeds maximum {self.max_idle_count}, clamping")
            idle_count = self.max_idle_count

        self.log.info(f"Configuring clock gating: enable={enable}, idle_count={idle_count}")

        # Use the AxiClockGateCtrl helper to configure the DUT
        self.cg_ctrl.enable_clock_gating(enable)
        self.cg_ctrl.set_idle_count(idle_count)

        # Wait a few cycles for configuration to take effect
        await self.wait_clocks('aclk', 5)

        # Verify configuration was applied correctly
        state = self.cg_ctrl.get_current_state()
        self.log.info(f"Clock gating state after configuration: {state}")

        # Return success if configuration was applied correctly
        return state['enabled'] == enable and state['idle_count'] == idle_count

    async def monitor_clock_gating(self, duration=500, units='ns'):
        """
        Monitor clock gating activity for a specified duration

        Args:
            duration: Duration to monitor
            units: Time units for duration ('ns', 'us', etc.)

        Returns:
            Dict with activity statistics
        """
        if not self.has_clock_gating:
            self.log.warning("Attempting to monitor clock gating on a DUT without support")
            return {}

        self.log.info(f"Monitoring clock gating activity for {duration} {units}")

        # Use the AxiClockGateCtrl helper to monitor activity
        stats = await self.cg_ctrl.monitor_activity(duration, units)

        # Log the results
        self.log.info("Activity monitoring complete:")
        self.log.info(f"  Active cycles: {stats['active_cycles']} ({stats.get('active_percent', 0):.1f}%)")
        self.log.info(f"  Gated cycles: {stats['gated_cycles']} ({stats.get('gated_percent', 0):.1f}%)")
        self.log.info(f"  User active: {stats['user_active_cycles']} ({stats.get('user_active_percent', 0):.1f}%)")
        self.log.info(f"  AXI active: {stats['axi_active_cycles']} ({stats.get('axi_active_percent', 0):.1f}%)")

        return stats

    async def verify_gating_after_inactivity(self, idle_count=None):
        """
        Verify that clock gating activates after the specified idle period

        Args:
            idle_count: Number of idle cycles to wait for gating (uses configured value if None)

        Returns:
            True if clock gating activated as expected
        """
        if not self.has_clock_gating:
            self.log.warning("Attempting to verify clock gating on a DUT without support")
            return False

        # Get current idle count if not specified
        if idle_count is None:
            state = self.cg_ctrl.get_current_state()
            idle_count = state['idle_count']

        self.log.info(f"Verifying clock gating activates after {idle_count} idle cycles")

        # Generate activity to wake up the clock
        await self.perform_write(addr=0x1000, data=0xDEADBEEF, id_value=0)

        # Wait a few cycles for the transaction to complete
        await self.wait_clocks('aclk', 20)

        # Wait for idle state
        idle_reached = await self.cg_ctrl.wait_for_idle(timeout=1000, units='ns')
        if not idle_reached:
            self.log.error("Failed to reach idle state within timeout")
            self.total_errors += 1
            return False

        self.log.info("Idle state reached, waiting for gating")

        # Wait for gating to activate (add a margin to the idle count)
        wait_cycles = idle_count + 10
        for _ in range(wait_cycles):
            # Check if gating is active
            state = self.cg_ctrl.get_current_state()
            if state['is_gated']:
                self.log.info(f"Clock gating activated after waiting {_} cycles")
                return True
            await self.wait_clocks('aclk', 1)

        # If we reached here, gating didn't activate in time
        self.log.error(f"Clock gating did not activate after waiting {wait_cycles} cycles")
        self.total_errors += 1
        return False

    async def verify_wakeup_from_gated(self):
        """
        Verify that the DUT wakes up from gated state when transaction arrives

        Returns:
            True if wakeup worked correctly
        """
        if not self.has_clock_gating:
            self.log.warning("Attempting to verify wakeup on a DUT without support")
            return False

        self.log.info("Verifying wakeup from gated state")

        # First ensure we're in gated state
        # Generate activity then wait for it to gate
        await self.perform_write(addr=0x2000, data=0x12345678, id_value=1)
        await self.wait_clocks('aclk', 20)

        # Wait for gating
        gating_reached = await self.cg_ctrl.wait_for_gating(timeout=1000, units='ns')
        if not gating_reached:
            self.log.error("Failed to reach gated state within timeout")
            self.total_errors += 1
            return False

        self.log.info("Gated state reached, sending wake-up transaction")

        # Check if we're gated (should be)
        state_before = self.cg_ctrl.get_current_state()
        if not state_before['is_gated']:
            self.log.error("Not in gated state before wake-up transaction")
            self.total_errors += 1
            return False

        # Send a transaction to wake up the clock
        await self.perform_write(addr=0x3000, data=0xABCDEF01, id_value=2)

        # Verify clock is no longer gated
        state_after = self.cg_ctrl.get_current_state()
        if state_after['is_gated']:
            self.log.error("Still in gated state after wake-up transaction")
            self.total_errors += 1
            return False

        self.log.info("Successfully woke up from gated state")

        return await self.verify_memory_value(0x3000, 0xABCDEF01)

    async def run_clock_gating_tests(self):
        """
        Run a series of tests to verify clock gating functionality

        Returns:
            True if all tests passed
        """
        if not self.has_clock_gating:
            self.log.warning("Skipping clock gating tests on a DUT without support")
            return True

        self.log.info("=" * 80)
        self.log.info("Running Clock Gating Tests")
        self.log.info("=" * 80)

        # Test 1: Basic functionality with clock gating disabled
        self.log.info("Test 1: Basic functionality with clock gating disabled")
        await self.configure_clock_gating(enable=False)
        await self.perform_write(addr=0x100, data=0xDEADBEEF, id_value=0)
        await self.perform_write(addr=0x200, data=[0x11111111, 0x22222222, 0x33333333, 0x44444444], id_value=1)

        # Monitor and verify no gating occurs
        stats = await self.monitor_clock_gating(duration=300, units='ns')
        if stats.get('gated_cycles', 0) > 0:
            self.log.error("Detected gating cycles when clock gating is disabled")
            self.total_errors += 1
            test1_passed = False
        else:
            self.log.info("Test 1 passed: No gating when disabled")
            test1_passed = True

        # Test 2: Basic functionality with default idle count
        self.log.info("Test 2: Basic functionality with default idle count")
        await self.configure_clock_gating(enable=True, idle_count=8)

        # Verify gating activates after inactivity
        test2_passed = await self.verify_gating_after_inactivity()
        if test2_passed:
            self.log.info("Test 2 passed: Gating activates after default idle count")

        # Test 3: Short idle count
        self.log.info("Test 3: Short idle count")
        short_idle = 2
        await self.configure_clock_gating(enable=True, idle_count=short_idle)

        # Verify gating activates after short inactivity
        test3_passed = await self.verify_gating_after_inactivity(short_idle)
        if test3_passed:
            self.log.info("Test 3 passed: Gating activates after short idle count")

        # Test 4: Long idle count
        self.log.info("Test 4: Long idle count")
        long_idle = min(16, self.max_idle_count)
        await self.configure_clock_gating(enable=True, idle_count=long_idle)

        # Verify gating activates after long inactivity
        test4_passed = await self.verify_gating_after_inactivity(long_idle)
        if test4_passed:
            self.log.info("Test 4 passed: Gating activates after long idle count")

        # Test 5: Wakeup from gated state
        self.log.info("Test 5: Wakeup from gated state")
        await self.configure_clock_gating(enable=True, idle_count=4)

        # Verify wakeup works correctly
        test5_passed = await self.verify_wakeup_from_gated()
        if test5_passed:
            self.log.info("Test 5 passed: Wakeup from gated state works correctly")

        # Test 6: Monitor activity during transactions
        self.log.info("Test 6: Monitor activity during transactions")
        await self.configure_clock_gating(enable=True, idle_count=8)

        # Start monitoring
        monitor_task = cocotb.start_soon(self.monitor_clock_gating(duration=1000, units='ns'))

        # Perform a series of transactions
        for i in range(5):
            addr = 0x4000 + (i * 0x100)
            data = 0xA0000000 + i
            await self.perform_write(addr=addr, data=data, id_value=i)
            # Add random delays between transactions
            await self.wait_clocks('aclk', random.randint(3, 12))

        # Wait for monitoring to complete
        stats = await monitor_task

        # Verify we saw both active and gated cycles
        if stats.get('active_cycles', 0) > 0 and stats.get('gated_cycles', 0) > 0:
            self.log.info("Test 6 passed: Detected both active and gated cycles")
            test6_passed = True
        else:
            self.log.error("Test 6 failed: Did not detect expected activity pattern")
            self.total_errors += 1
            test6_passed = False

        # Overall test result
        all_passed = test1_passed and test2_passed and test3_passed and test4_passed and test5_passed and test6_passed

        self.log.info("=" * 80)
        self.log.info(f"Clock Gating Tests: {'PASSED' if all_passed else 'FAILED'}")
        self.log.info("=" * 80)

        return all_passed

    def _log_config(self):
        """Log the testbench configuration"""
        self.log.info("=" * 80)
        self.log.info("AXI4 Master Write Testbench Configuration:")
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
            channels=["AW", "W", "B"],  # Write channels only
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width,
            log=self.log
        )

        # Set randomizers for individual channels
        self.fub_master.aw_master.set_randomizer(self.fub_randomizer)
        self.fub_master.w_master.set_randomizer(self.fub_randomizer)
        self.fub_master.b_slave.set_randomizer(self.fub_randomizer)

        # Create AXI4 Slave for the AXI4 side (output)
        self.axi_slave = create_axi4_slave(
            dut=self.dut,
            title="axi_slave",
            prefix="m_axi",
            divider="",
            suffix="",
            clock=self.dut.aclk,
            channels=["AW", "W", "B"],  # Write channels only
            memory_model=self.mem,
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width,
            log=self.log
        )

        # Set randomizers for individual channels
        self.axi_slave.aw_slave.set_randomizer(self.axi_randomizer)
        self.axi_slave.w_slave.set_randomizer(self.axi_randomizer)
        self.axi_slave.b_master.set_randomizer(self.axi_randomizer)

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
            error_type_str += "AW_TIMEOUT "
        if error_type & 0x2:
            error_type_str += "W_TIMEOUT "
        if error_type & 0x4:
            error_type_str += "B_TIMEOUT "
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

    async def perform_write(self, addr, data, id_value=0, burst_len=None, burst_size=None, strb=None):
        """
        Perform a write transaction with the given parameters

        Args:
            addr: Address to write to
            data: Data to write (single value or list for burst)
            id_value: AXI ID for the transaction
            burst_len: Burst length (calculated from data if None)
            burst_size: Size (log2 of bytes), defaults to max for data width
            strb: Byte strobes (optional)

        Returns:
            The result dictionary from the write operation
        """
        # Handle data as single value or list
        if not isinstance(data, list):
            data = [data]

        # If burst_len not specified, calculate from data length
        if burst_len is None:
            burst_len = len(data) - 1

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
            'data': data,
            'burst_len': burst_len,
            'burst_size': burst_size,
            'status': 'STARTED',
            'response': None,
            'splits': [],
            'errors': []
        }

        self.log.info(f"Performing write: addr=0x{addr:X}, id={id_value}, data[0]=0x{data[0]:X}, burst_len={burst_len}, burst_size={burst_size}")

        # Perform the write
        result = await self.fub_master.write(
            addr=addr,
            data=data,
            id=id_value,
            burst=burst_type,  # INCR
            length=burst_len,
            size=burst_size,
            strobe=strb
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

    async def verify_memory_value(self, addr, expected_value, burst_size=None):
        """
        Verify that memory contains the expected value at the address

        Args:
            addr: Address to check
            expected_value: Expected value
            burst_size: Size (log2 of bytes), defaults to max for data width

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

        # Read expected value from memory
        expected_bytes = self.mem.read(addr, bytes_per_transfer)
        actual_value = self.mem.bytearray_to_integer(expected_bytes)

        # For smaller transfer sizes, we need to extract the correct bytes
        # The data alignment depends on the address
        byte_offset = addr % self.strb_width
        bit_offset = byte_offset * 8

        # For transfers smaller than full data width, extract the appropriate bytes
        if bytes_per_transfer < self.strb_width:
            # Extract the relevant bytes based on size and address alignment
            masked_actual = (actual_value >> bit_offset) & size_mask
            masked_expected = expected_value & size_mask
        else:
            # For full-width transfers, use the entire value
            masked_actual = actual_value
            masked_expected = expected_value

        # Compare
        if masked_actual != masked_expected:
            self.log.error(f"Data mismatch at addr=0x{addr:X}: "
                        f"expected=0x{masked_expected:X}, found=0x{masked_actual:X}")
            self.total_errors += 1
            return False
        else:
            self.log.debug(f"Data match at addr=0x{addr:X}: "
                        f"value=0x{masked_actual:X}")
            return True

    async def verify_split_transaction(self, result, addr, id_value, burst_len, burst_size, expected_splits):
        """
        Verify that transaction was split correctly

        Args:
            result: Result from write operation
            addr: Address written to
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

        # Also verify the data to make sure it was written correctly despite the split
        if isinstance(txn_info['data'], list):
            data_match = True
            for i, value in enumerate(txn_info['data']):
                current_addr = addr + (i * (1 << burst_size))
                value_match = await self.verify_memory_value(current_addr, value, burst_size)
                data_match = data_match and value_match
        else:
            data_match = await self.verify_memory_value(addr, txn_info['data'], burst_size)

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
        if channel.lower() in ['aw', 'w']:
            # Address or data channel
            base_timeout = self.timeout_aw if channel.lower() == 'aw' else self.timeout_w
        else:
            # Response channel (B)
            base_timeout = self.timeout_b

        # Apply factor to ensure delay exceeds timeout
        min_delay = int(int(base_timeout) * timeout_factor)
        max_delay = min_delay + 50  # Add some variability

        delay_config = {
            f'{channel}_delay': ([[min_delay, max_delay]], [1.0])
        }

        patho_randomizer = FlexRandomizer(delay_config)

        if interface.lower() == 'fub':
            if channel.lower() == 'aw':
                self.fub_master.aw_master.set_randomizer(patho_randomizer)
            elif channel.lower() == 'w':
                self.fub_master.w_master.set_randomizer(patho_randomizer)
            else:  # 'b'
                self.fub_master.b_slave.set_randomizer(patho_randomizer)
            self.log.info(f"Set pathological {channel} delay on FUB {interface} channel: {min_delay}-{max_delay} cycles")
        else:  # 'axi'
            if channel.lower() == 'aw':
                self.axi_slave.aw_slave.set_randomizer(patho_randomizer)
            elif channel.lower() == 'w':
                self.axi_slave.w_slave.set_randomizer(patho_randomizer)
            else:  # 'b'
                self.axi_slave.b_master.set_randomizer(patho_randomizer)
            self.log.info(f"Set pathological {channel} delay on AXI {interface} channel: {min_delay}-{max_delay} cycles")

        # Wait for setting to take effect
        await self.wait_clocks('aclk', 5)

    async def wait_for_timeout_detection(self, timeout_type='aw', additional_margin=20):
        """
        Wait for a sufficient number of cycles for timeout detection

        Args:
            timeout_type: 'aw' for address channel timeout, 'w' for data channel timeout, 'b' for response timeout
            additional_margin: Additional cycles to wait beyond the timeout value

        Returns:
            Number of cycles waited
        """
        if timeout_type.lower() == 'aw':
            timeout_cycles = self.timeout_aw
        elif timeout_type.lower() == 'w':
            timeout_cycles = self.timeout_w
        else:  # 'b'
            timeout_cycles = self.timeout_b

        wait_cycles = int(timeout_cycles) + int(additional_margin)
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

        # Get all write transactions from the sequence
        write_ids = sequence.get_write_ids()

        # Execute each write transaction
        for write_id in write_ids:
            # Get the write address packet
            aw_packet = sequence.get_write_addr_packet(write_id)
            if not aw_packet:
                continue

            # Get the write data packets
            w_packets = sequence.get_write_data_packets(write_id)
            if not w_packets:
                continue

            # Extract parameters
            addr = aw_packet.awaddr
            burst_len = aw_packet.awlen
            burst_size = aw_packet.awsize

            # Extract data values from packets
            data_values = [pkt.wdata for pkt in w_packets]

            # Extract strobe values from packets if available
            strb_values = [pkt.wstrb for pkt in w_packets] if hasattr(w_packets[0], 'wstrb') else None

            # Perform the write
            result = await self.perform_write(
                addr=addr,
                data=data_values,
                id_value=write_id,
                burst_len=burst_len,
                burst_size=burst_size,
                strb=strb_values
            )

            # Verify data by checking memory
            for i, data_value in enumerate(data_values):
                current_addr = addr + (i * (1 << burst_size))
                await self.verify_memory_value(current_addr, data_value, burst_size)

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
                    channel="AW",  # For write tests
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

    async def test_error_monitor_basic(self):
        """
        Basic test for error monitor functionality in AXI Master WR

        This test verifies basic error detection and reporting in the error monitor
        including address timeouts, data timeouts, response timeouts, and response errors.
        """
        # Save original randomizers
        original_fub_aw_randomizer = self.fub_master.aw_master.get_randomizer()
        original_fub_w_randomizer = self.fub_master.w_master.get_randomizer()
        original_fub_b_randomizer = self.fub_master.b_slave.get_randomizer()
        original_axi_aw_randomizer = self.axi_slave.aw_slave.get_randomizer()
        original_axi_w_randomizer = self.axi_slave.w_slave.get_randomizer()
        original_axi_b_randomizer = self.axi_slave.b_master.get_randomizer()

        # 1. Test Address Timeout
        self.log.info('='*80)
        self.log.info('Error Test: AW Timeout')
        self.log.info('='*80)

        # Configure AXI slave to introduce long delay on AW ready
        aw_timeout = self.timeout_aw
        slow_aw_ready_config = {
            'ready_delay': ([[int(aw_timeout * 2.1), int(aw_timeout * 2.1)]], [1.0])
        }
        self.axi_slave.aw_slave.set_randomizer(FlexRandomizer(slow_aw_ready_config))
        self.axi_slave.w_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fixed']['read']))
        self.axi_slave.b_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fixed']['write']))

        # Reset and setup for clean test state
        await self.reset_dut()

        # Attempt a write that will timeout on address channel
        addr_start = 0x4000
        count = self.skid_depth_aw + 1
        id_value = 0

        # Calculate the decrement size based on count
        addr_decrement = 0x100  # Example decrement value
        starting_offset = (count - 1) * addr_decrement

        # Loop from highest address down to lowest
        for i in range(count):
            addr = addr_start - starting_offset + (i * addr_decrement)
            try:
                # Send just the AW phase and don't wait for response
                from CocoTBFramework.components.axi4.axi4_packet import AXI4Packet

                aw_packet = AXI4Packet.create_aw_packet(
                    awid=id_value,
                    awaddr=addr,
                    awlen=0,
                    awsize=2,
                    awburst=1,
                    awlock=0,
                    awcache=0,
                    awprot=0,
                    awqos=0,
                    awregion=0,
                    awuser=0
                )
                await self.fub_master.aw_master.send(aw_packet)

            except Exception as e:
                self.log.info(f"Expected exception: {str(e)}")

        # Wait for address phase to complete
        while self.fub_master.aw_master.transfer_busy:
            await self.wait_clocks('aclk', 1)

        # Verify error was reported with correct address and ID
        aw_timeout_detected = await self.verify_error_addresses(
            txn_id=id_value,
            expected_addr=addr_start,
            error_type=0x1  # AW timeout
        )

        # Reset DUT for clean state before next test
        await self.reset_dut()
        await self.start_components()

        # 2. Test Data Timeout
        self.log.info('='*80)
        self.log.info('Error Test: W Timeout')
        self.log.info('='*80)

        # Configure AXI slave to introduce long delay on W ready
        w_timeout = self.timeout_w
        slow_w_ready_config = {
            'ready_delay': ([[int(w_timeout * 2.1), int(w_timeout * 2.1)]], [1.0])
        }
        self.axi_slave.w_slave.set_randomizer(FlexRandomizer(slow_w_ready_config))
        self.axi_slave.aw_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fixed']['read']))
        self.axi_slave.b_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fixed']['write']))

        # Reset and setup for clean test state
        await self.reset_dut()
        await self.start_components()

        # Attempt writes that will timeout on data channel
        addr_start = 0x5000
        count = 1
        awlen = self.skid_depth_w - 1
        id_value = 1

        # Calculate the decrement size
        addr_decrement = 0x100
        starting_offset = (count - 1) * addr_decrement

        # Loop from lowest address up to highest
        for i in range(count):
            addr = addr_start - starting_offset + (i * addr_decrement)
            self.log.info(f"Starting write that will timeout on data channel: addr=0x{addr:X}, id={id_value}")

            try:
                # Create write data - need enough for the burst
                data_values = [(0xA0000000 + j) for j in range(awlen + 1)]

                # Send the AW packet
                aw_packet = AXI4Packet.create_aw_packet(
                    awid=id_value,
                    awaddr=addr,
                    awlen=awlen,
                    awsize=2,
                    awburst=1,
                    awlock=0,
                    awcache=0,
                    awprot=0,
                    awqos=0,
                    awregion=0,
                    awuser=0
                )
                await self.fub_master.aw_master.send(aw_packet)

                # Wait for address phase to complete
                while self.fub_master.aw_master.transfer_busy:
                    await self.wait_clocks('aclk', 1)

                # Send W packets
                for j, data in enumerate(data_values):
                    w_packet = AXI4Packet.create_w_packet(
                        wdata=data,
                        wstrb=0xFF,
                        wlast=(j == len(data_values) - 1),
                        wuser=0
                    )
                    await self.fub_master.w_master.send(w_packet)

            except Exception as e:
                self.log.info(f"Expected exception: {str(e)}")

        # Wait for data phase to complete
        while self.fub_master.w_master.transfer_busy:
            await self.wait_clocks('aclk', 1)

        # Wait for timeout to be detected (timeout + margin)
        await self.wait_clocks('aclk', w_timeout + 20)

        # Verify error was reported with correct address and ID
        w_timeout_detected = await self.verify_error_addresses(
            txn_id=id_value,
            expected_addr=addr_start,
            error_type=0x2  # W timeout
        )

        # 3. Test Response Timeout
        self.log.info('='*80)
        self.log.info('Error Test: B Timeout')
        self.log.info('='*80)

        # Configure AXI slave to introduce long delay on B valid
        b_timeout = self.timeout_b
        slow_b_valid_config = {
            'valid_delay': ([[int(b_timeout * 2.1), int(b_timeout * 2.1)]], [1.0])
        }
        self.axi_slave.b_master.set_randomizer(FlexRandomizer(slow_b_valid_config))
        self.axi_slave.aw_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fixed']['read']))
        self.axi_slave.w_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fixed']['read']))

        # Reset and setup for clean test state
        await self.reset_dut()
        await self.start_components()

        # Attempt a write that will timeout on response channel
        addr_start = 0x6000
        id_value = 2

        try:
            # Create simple write
            data_value = 0xB0B0B0B0

            # Set up the fub_master.b_slave to not accept responses (this forces the timeout)
            self.fub_master.b_slave.set_randomizer(FlexRandomizer({'ready_delay': ([[int(b_timeout * 2.1), int(b_timeout * 2.1)]], [1.0])}))

            # Start the write
            aw_packet = AXI4Packet.create_aw_packet(
                awid=id_value,
                awaddr=addr_start,
                awlen=0,  # Single beat
                awsize=2,
                awburst=1,
                awlock=0,
                awcache=0,
                awprot=0,
                awqos=0,
                awregion=0,
                awuser=0
            )
            await self.fub_master.aw_master.send(aw_packet)

            # Send W packet
            w_packet = AXI4Packet.create_w_packet(
                wdata=data_value,
                wstrb=0xFF,
                wlast=1,
                wuser=0
            )
            await self.fub_master.w_master.send(w_packet)

        except Exception as e:
            self.log.info(f"Expected exception: {str(e)}")

        # Wait for timeout to be detected (timeout + margin)
        await self.wait_clocks('aclk', b_timeout + 20)

        # Verify error was reported with correct address and ID
        b_timeout_detected = await self.verify_error_addresses(
            txn_id=id_value,
            expected_addr=addr_start,
            error_type=0x4  # B timeout
        )

        # 4. Test Response Error
        self.log.info('='*80)
        self.log.info('Error Test: Response error detection')
        self.log.info('='*80)

        # Reset the randomizers to normal
        self.axi_slave.aw_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fixed']['read']))
        self.axi_slave.w_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fixed']['read']))
        self.axi_slave.b_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fixed']['write']))
        self.fub_master.b_slave.set_randomizer(original_fub_b_randomizer)

        error_handler = self.axi_slave.extensions['error_handler']

        # Reset and setup for clean test state
        await self.reset_dut()
        await self.start_components()

        # Set up the slave to return error responses
        self.axi_slave.error_rate = 1.0

        # Send multiple transactions to test error responses
        addr_start = 0x7000
        count = min(4, self.channels)  # Test multiple channels

        # Send transactions to different IDs
        for i in range(count):
            addr = addr_start + (i * 0x100)
            id_value = i + 3  # Start from ID 3

            self.log.info(f"Sending transaction for response error: addr=0x{addr:X}, id={id_value}")

            # register an error
            error_handler.register_error_transaction(addr, id_value, 2)

            # Create a simple write
            data_value = 0xC0000000 + i

            await self.perform_write(
                addr=addr,
                data=data_value,
                id_value=id_value
            )

        # Wait for responses to be processed
        await self.wait_clocks('aclk', 20)

        # Verify errors for each transaction
        resp_errors_detected = True
        for i in range(count):
            id_value = i + 3
            addr = addr_start + (i * 0x100)

            error_detected = await self.verify_error_addresses(
                txn_id=id_value,
                expected_addr=addr,
                error_type=0x8  # Response error
            )

            if not error_detected:
                resp_errors_detected = False

        # clear the errors
        error_handler.clear_error_transactions()

        # Restore original randomizers
        self.fub_master.aw_master.set_randomizer(original_fub_aw_randomizer)
        self.fub_master.w_master.set_randomizer(original_fub_w_randomizer)
        self.fub_master.b_slave.set_randomizer(original_fub_b_randomizer)
        self.axi_slave.aw_slave.set_randomizer(original_axi_aw_randomizer)
        self.axi_slave.w_slave.set_randomizer(original_axi_w_randomizer)
        self.axi_slave.b_master.set_randomizer(original_axi_b_randomizer)
        self.axi_slave.error_rate = 0.0

        # Return overall success
        return aw_timeout_detected and w_timeout_detected and b_timeout_detected and resp_errors_detected

    async def test_error_monitor_flow_control(self):
        """
        Test flow control via int_block_ready signal

        This test verifies that int_block_ready is asserted when the address tracking
        FIFOs are full and deasserted when entries are removed.
        """
        self.log.info('='*80)
        self.log.info('Error Test: Flow Control')
        self.log.info('='*80)

        # Set a more predictable randomizer for the B channel
        self.fub_master.b_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fixed']['read']))

        # Reset and setup for clean test state
        await self.reset_dut()

        # Fill the address tracking FIFOs to capacity plus skid buffer depth
        total_capacity = max(self.error_fifo_depth, self.skid_depth_aw)

        # Keep track of block_ready assertions
        block_ready_assertions = []

        # Register edge detector for int_block_ready
        async def monitor_block_ready():
            previous = self.block_ready.value

            while True:
                await Edge(self.block_ready)
                current = self.block_ready.value

                if current and not previous:  # Rising edge
                    block_ready_assertions.append("asserted")
                    self.log.info(f"int_block_ready asserted @ {cocotb.utils.get_sim_time('ns')}ns")
                elif not current and previous:  # Falling edge
                    block_ready_assertions.append("deasserted")
                    self.log.info(f"int_block_ready deasserted @ {cocotb.utils.get_sim_time('ns')}ns")

                previous = current

        # Start monitor
        block_ready_task = cocotb.start_soon(monitor_block_ready())

        # Save original randomizers
        original_fub_w_randomizer = self.fub_master.w_master.get_randomizer()

        # Set W channel to not accept data
        # This ensures address phases complete but data doesn't drain
        self.fub_master.w_master.set_randomizer(FlexRandomizer({'valid_delay': ([[100, 100]], [1.0])}))
        id_value = random.randint(0, self.channels-1)

        # Send transactions to fill FIFO (more than capacity to ensure we hit the limit)
        for i in range(total_capacity + 2):
            addr = 0x8000 + (i * 0x100)

            self.log.info(f"Sending transaction {i+1}/{total_capacity+2}: addr=0x{addr:X}, id={id_value}")

            # Create and send AW packet
            from CocoTBFramework.components.axi4.axi4_packet import AXI4Packet

            aw_packet = AXI4Packet.create_aw_packet(
                awid=id_value,
                awaddr=addr,
                awlen=0,
                awsize=2,
                awburst=1,
                awlock=0,
                awcache=0,
                awprot=0,
                awqos=0,
                awregion=0,
                awuser=0
            )
            await self.fub_master.aw_master.send(aw_packet)

            # Wait for address phase to complete or block_ready to assert
            timeout = 0
            max_timeout = 100
            while self.fub_master.aw_master.transfer_busy and timeout < max_timeout:
                if self.block_ready.value:
                    self.log.info(f"int_block_ready asserted during transaction {i+1}")
                    break
                await self.wait_clocks('aclk', 1)
                timeout += 1

            # If block_ready asserted, we've hit our goal
            if self.block_ready.value:
                self.log.info(f"int_block_ready asserted after {i+1} transactions")
                break

        # Wait a bit to ensure any final block_ready assertion is captured
        await self.wait_clocks('aclk', 10)

        # Verify block_ready was asserted
        if "asserted" not in block_ready_assertions:
            self.log.error("int_block_ready was never asserted")
            return False

        # Now allow data to flow to drain the FIFOs
        self.fub_master.w_master.set_randomizer(original_fub_w_randomizer)

        # Wait for block_ready to deassert
        max_wait = 1000
        for _ in range(max_wait):
            if not self.block_ready.value:
                break
            await self.wait_clocks('aclk', 1)

        # Verify block_ready was deasserted
        if "deasserted" not in block_ready_assertions:
            self.log.error("int_block_ready was never deasserted")
            return False

        # Clean up
        block_ready_task.kill()

        return True

    async def test_error_monitor_address_tracking(self):
        """
        Test that errors report the correct address

        This test verifies that the error monitor correctly tracks addresses
        through the FIFOs for error reporting.
        """
        self.log.info('='*80)
        self.log.info('Error Test: Address Tracking')
        self.log.info('='*80)

        # Reset and setup for clean test state
        await self.reset_dut()

        # Save original randomizers
        original_axi_b_randomizer = self.axi_slave.b_master.get_randomizer()
        error_handler = self.axi_slave.extensions['error_handler']

        # Configure AXI slave to return error responses
        self.axi_slave.error_rate = 1.0

        # Dictionary to track sent transactions
        sent_transactions = {}

        # Send multiple transactions with different addresses and IDs
        # Account for both the FIFO depth and skid buffer
        total_capacity = self.error_fifo_depth + self.skid_depth_aw
        num_transactions = min(total_capacity, self.channels, 8)  # Test reasonable number

        # Send the transactions
        for i in range(num_transactions):
            addr = 0xA000 + (i * 0x1000)
            id_value = i % self.channels

            sent_transactions[id_value] = addr

            self.log.info(
                f"Sending transaction {id_value + 1}/{num_transactions}: addr=0x{addr:X}, id={id_value}"
            )

            # register an error
            error_handler.register_error_transaction(addr, id_value, 2)

            # Send a simple write
            data_value = 0xD0000000 + i
            await self.perform_write(addr, data_value, id_value)

        # Wait for all transactions to complete or timeout
        await self.wait_clocks('aclk', 200)

        # Verify error addresses for each transaction
        all_correct = True
        for id_value, addr in sent_transactions.items():
            # Verify error was reported with correct address and ID
            error_correct = await self.verify_error_addresses(
                txn_id=id_value,
                expected_addr=addr,
                error_type=0x8  # Response error
            )

            if not error_correct:
                all_correct = False

        # Restore normal operation
        self.axi_slave.error_rate = 0.0
        self.axi_slave.b_master.set_randomizer(original_axi_b_randomizer)

        return all_correct

    async def run_error_monitor_tests(self):
        """
        Run all error monitor tests and report results
        """
        self.log.info("=" * 80)
        self.log.info("Running AXI Error Monitor Tests")
        self.log.info("=" * 80)

        # Reset error count
        initial_errors = self.total_errors

        # Run the tests
        basic_passed = await self.test_error_monitor_basic()
        self.log.info(f"Basic Error Monitor Test: {'PASSED' if basic_passed else 'FAILED'}")

        # Reset for next test
        await self.reset_dut()
        await self.start_components()

        flow_control_passed = await self.test_error_monitor_flow_control()
        self.log.info(f"Flow Control Test: {'PASSED' if flow_control_passed else 'FAILED'}")

        # Reset for next test
        await self.reset_dut()
        await self.start_components()

        address_tracking_passed = await self.test_error_monitor_address_tracking()
        self.log.info(f"Address Tracking Test: {'PASSED' if address_tracking_passed else 'FAILED'}")

        # Reset for next test
        await self.reset_dut()
        await self.start_components()

        # Report overall results
        tests_passed = basic_passed and flow_control_passed and address_tracking_passed
        final_errors = self.total_errors

        self.log.info("=" * 80)
        self.log.info(f"Error Monitor Tests: {'PASSED' if tests_passed else 'FAILED'}")
        self.log.info(f"Error Count: {final_errors - initial_errors}")
        self.log.info("=" * 80)

        return tests_passed

    async def run_basic_test(self):
        """Run basic functionality tests without transaction splitting"""
        self.log.info("Running basic functionality test")

        # Test 1: Single-beat write transactions

        self.log.info("=" * 80)
        self.log.info(f"Test 1: Single-beat write transactions{self.get_time_ns_str()}")
        self.log.info("=" * 80)
        self.axi_slave.b_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fixed']['write']))
        self.reset_dut()

        for i in range(5):
            addr = i * 0x100  # Space out addresses
            data = 0xA0000000 + i
            result = await self.perform_write(addr=addr, data=data, id_value=i)
            await self.verify_memory_value(addr, data)
            await self.wait_clocks('aclk', 5)  # Wait between transactions

        # Test 2: Burst write transactions
        self.log.info("=" * 80)
        self.log.info(f"Test 2: Burst write transactions{self.get_time_ns_str()}")
        self.log.info("=" * 80)
        for i, burst_len in enumerate([1, 3, 7]):  # 2, 4, 8 beats
            addr = 0x1000 + (i * 0x100)  # Ensure no boundary crossing
            data = [(0xB0000000 + i*100 + j) for j in range(burst_len + 1)]
            result = await self.perform_write(addr=addr, data=data, id_value=10+i, burst_len=burst_len)

            # Verify each value in memory
            for j, value in enumerate(data):
                current_addr = addr + (j * (self.data_width // 8))
                await self.verify_memory_value(current_addr, value)

            await self.wait_clocks('aclk', 10)  # Longer wait for burst transactions

        # Test 3: Different burst sizes
        self.log.info("=" * 80)
        self.log.info(f"Test 3: Different burst sizes{self.get_time_ns_str()}")
        self.log.info("=" * 80)
        for i, burst_size in enumerate([0, 1, 2]):  # 1, 2, 4 bytes
            addr = 0x2000 + (i * 0x100)
            data = 0xC0000000 + i
            result = await self.perform_write(addr=addr, data=data, id_value=20+i, burst_size=burst_size)
            await self.verify_memory_value(addr, data, burst_size)
            await self.wait_clocks('aclk', 5)

        return self.get_test_result()

    async def run_split_test(self):
        """Run transaction splitting tests with different alignment masks"""
        self.log.info("Running transaction splitting test")

        # Test with different alignment masks
        alignment_masks = [
            0xFFF,  # 4K boundary (default)
            0x7FF,  # 2K boundary
            0x3FF,  # 1K boundary
            0x1FF,  # 512-byte boundary
        ]

        # Manual tests for specific boundary cases
        for mask in alignment_masks:
            # Set alignment mask
            await self.set_alignment_mask(mask)
            boundary = mask + 1

            self.log.info(f"Testing with alignment mask: 0x{mask:X}")

            # Test 1: Transaction directly before boundary
            addr = boundary - 16  # Place just before boundary
            burst_len = 7  # 8 beats
            data = [(0xD0000000 + i) for i in range(burst_len + 1)]

            # Execute the write
            result = await self.perform_write(addr=addr, data=data, id_value=0, burst_len=burst_len)

            # Verify split and data
            expected_splits = self.calculate_expected_splits(addr, burst_len, 2)
            await self.verify_split_transaction(result, addr, 0, burst_len, 2, expected_splits)

            # Test 2: Transaction spanning multiple boundaries
            addr = boundary - 32
            burst_len = 15  # 16 beats (spans multiple boundaries)
            data = [(0xE0000000 + i) for i in range(burst_len + 1)]

            # Execute the write
            result = await self.perform_write(addr=addr, data=data, id_value=1, burst_len=burst_len)

            # Verify split and data
            expected_splits = self.calculate_expected_splits(addr, burst_len, 2)
            await self.verify_split_transaction(result, addr, 1, burst_len, 2, expected_splits)

            # Wait between masks
            await self.wait_clocks('aclk', 20)
            await self.axi_slave.debug_dump_state()

        # Run the comprehensive boundary test with multiple pages
        page_addresses = [0, 0x10000, 0x20000]  # Test multiple pages
        await self.run_boundary_test_sequence(masks=alignment_masks, page_addresses=page_addresses)

        # Return the test result
        return self.get_test_result()

    async def run_full_test(self):
        """Run comprehensive test of all features"""
        self.log.info("Running comprehensive test")
        await self.configure_slave_response_order(inorder=True)

        # Part 1: Basic functionality
        self.log.info("Part 1: Basic functionality")
        basic_result = await self.run_basic_test()

        # Reset before next test
        await self.reset_dut()
        await self.start_components()

        # Part 2: Clock Gating
        self.log.info("Part 2: Clock Gating")
        cg_result = await self.run_clock_gating_tests()

        # Reset before next test
        await self.reset_dut()
        await self.start_components()

        # Part 3: Transaction splitting
        self.log.info("Part 3: Transaction splitting")
        split_result = await self.run_split_test()

        # Reset before next test
        await self.reset_dut()
        await self.start_components()

        # Part 4: Error detection
        self.log.info("Part 4: Error detection")
        error_result = await self.run_error_monitor_tests()

        # Reset before next test
        await self.reset_dut()
        await self.start_components()

        # Part 5: Out-of-order response handling
        self.log.info("Part 5: Out-of-order response handling")

        # Toggle to out-of-order responses
        await self.configure_slave_response_order(inorder=False)

        # Create sequence with multiple IDs
        ooo_sequence = AXI4TransactionSequence(
            name="multi_id_sequence",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width
        )

        # Add writes with different IDs
        for i in range(8):
            addr = 0x2000 + (i * 0x40)
            ooo_sequence.add_write_transaction(
                addr=addr,
                data_values=[0xF0000000 + i, 0xF1000000 + i, 0xF2000000 + i, 0xF3000000 + i],
                id_value=i,
                burst_len=3  # 4 beats
            )

        # Run the sequence
        await self.run_transaction_sequence(ooo_sequence)
        ooo_result = self.get_test_result()

        # Part 6: Randomized testing
        self.log.info("Part 6: Randomized testing")

        # Create and run random transactions with different delay profiles
        delay_profiles = ['constrained', 'burst_pause', 'slow_consumer']
        for profile in delay_profiles:
            # Set randomizers for each channel
            # FUB master side (AW master, W master, B slave)
            self.fub_master.aw_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[profile]['write']))
            self.fub_master.w_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[profile]['write']))
            self.fub_master.b_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[profile]['read']))

            # AXI slave side (AW slave, W slave, B master)
            self.axi_slave.aw_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[profile]['read']))
            self.axi_slave.w_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[profile]['read']))
            self.axi_slave.b_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[profile]['write']))

            # Create random sequence
            rand_sequence = AXI4TransactionSequence(
                name="random_sequence",
                id_width=self.id_width,
                addr_width=self.addr_width,
                data_width=self.data_width
            )

            # Add random write transactions
            for i in range(10):
                addr = random.randint(0x1000, 0x8FFF) & ~0x3  # Align to word
                id_value = random.randint(0, 7)
                burst_len = random.choice([0, 1, 3, 7])  # Random burst length
                data = [(0xA0A00000 + i*100 + j) for j in range(burst_len + 1)]

                rand_sequence.add_write_transaction(
                    addr=addr,
                    data_values=data,
                    id_value=id_value,
                    burst_len=burst_len
                )

            # Run sequence
            await self.run_transaction_sequence(rand_sequence)
            await self.wait_clocks('aclk', 30)

        random_result = self.get_test_result()

        # Check all results
        return basic_result and cg_result and split_result and error_result and ooo_result and random_result

    async def run_selected_test(self):
        """Run the selected test type"""
        if self.test_type == 'basic':
            return await self.run_basic_test()
        elif self.test_type == 'clock_gating':
            return await self.run_clock_gating_tests()
        elif self.test_type == 'splits':
            return await self.run_split_test()
        elif self.test_type == 'error':
            return await self.run_error_monitor_tests()
        elif self.test_type == 'full':
            return await self.run_full_test()
        else:
            self.log.error(f"Unknown test type: {self.test_type}")
            return False
