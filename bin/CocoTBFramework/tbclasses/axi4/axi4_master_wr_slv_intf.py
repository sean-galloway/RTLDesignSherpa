"""
AXI4 Master Write AXI4 Interface

This module provides a testbench interface for the AXI4 interfaces
of the AXI4 Master Write module, specifically focusing on the s_axi and m_axi
interfaces for write transactions.
"""

import cocotb
import random
from cocotb.triggers import Timer

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_master, create_axi4_slave, create_axi4_monitor
)
from CocoTBFramework.components.axi4.axi4_packets import AXI4Packet
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.components.debug_object import get_object_details

class Axi4MasterWrAxi4Intf(TBBase):
    """
    Interface for the AXI4 interfaces of the AXI4 Master Write module.
    This class handles the slave and master AXI4 interfaces that carry
    the actual write requests and responses.
    """

    def __init__(self, dut, memory_model=None):
        """
        Initialize the AXI4 Master Write AXI4 Interface.

        Args:
            dut: Device under test
            memory_model: Optional memory model for backing storage (will create one if None)
        """
        super().__init__(dut)

        # Extract parameters from the DUT or use defaults
        self.id_width = int(getattr(dut, 'AXI_ID_WIDTH', 8))
        self.addr_width = int(getattr(dut, 'AXI_ADDR_WIDTH', 32))
        self.data_width = int(getattr(dut, 'AXI_DATA_WIDTH', 32))
        self.user_width = int(getattr(dut, 'AXI_USER_WIDTH', 1))
        self.timeout_aw = int(getattr(dut, 'TIMEOUT_AW', 1000))
        self.timeout_w = int(getattr(dut, 'TIMEOUT_W', 1000))
        self.timeout_b = int(getattr(dut, 'TIMEOUT_B', 1000))

        # Set the max boundary
        self.boundary_4k = 0xFFF

        # Calculate strobe width
        self.strb_width = self.data_width // 8

        # Set the burst type
        self.burst = 0x1

        # Calculate size parameter based on data width
        self.dsize = 0  # Default to byte access
        temp_width = self.data_width // 8  # Convert to bytes
        while temp_width > 1:
            temp_width >>= 1
            self.dsize += 1

        # Create memory model if not provided
        if memory_model is None:
            self.memory_model = MemoryModel(
                num_lines=32768,  # 128K memory
                bytes_per_line=self.strb_width,
                log=self.log
            )
            self.owns_memory_model = True
        else:
            self.memory_model = memory_model
            self.owns_memory_model = False

        # Initialize memory with a pattern
        self._initialize_memory()

        # Create randomizers for different test scenarios
        self.randomizers = self._create_randomizers()
        channels = ['aw', 'w', 'b']

        # Create AXI4 master component for the slave interface (s_axi_*)
        self.s_axi_master = create_axi4_master(
            dut, "S_AXI_Master",
            prefix='s_axi',
            divider='',
            suffix='',
            clock=dut.aclk,
            channels=channels,
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width,
            randomizers={'aw': self.randomizers['aw_fast'], 'w': self.randomizers['w_fast']},
            log=self.log
        )

        # Create AXI4 slave component for the master interface (m_axi_*)
        self.m_axi_slave = create_axi4_slave(
            dut, "M_AXI_Slave",
            prefix='m_axi',
            divider='',
            suffix='',
            clock=dut.aclk,
            channels=channels,
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width,
            memory_model=self.memory_model,
            randomizers={'b': self.randomizers['b_fast']},
            log=self.log
        )

        # Create monitors for both interfaces
        self.s_axi_monitor = create_axi4_monitor(
            dut, "S_AXI_Monitor",
            prefix='s_axi',
            divider='',
            suffix='',
            clock=dut.aclk,
            channels=channels,
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width,
            is_slave_side=True,
            log=self.log
        )

        self.m_axi_monitor = create_axi4_monitor(
            dut, "M_AXI_Monitor",
            prefix='m_axi',
            divider='',
            suffix='',
            clock=dut.aclk,
            channels=channels,
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width,
            is_slave_side=False,
            log=self.log
        )

        # Connect monitors to callbacks for tracking transactions
        self.s_axi_monitor.set_write_callback(self._handle_s_axi_write)
        self.m_axi_monitor.set_write_callback(self._handle_m_axi_write)

        # Create command handler to connect AW and W channels
        self.cmd_handler = None  # Will be initialized later in start_command_handler

        # Transaction tracking
        self.pending_writes = {}  # Writes sent to DUT, awaiting response
        self.completed_writes = {}  # Completed write transactions
        self.m_axi_aw_transactions = []  # AW transactions on m_axi interface
        self.m_axi_w_transactions = []  # W transactions on m_axi interface

        # ID counter for generating unique transaction IDs
        self.next_id = 0

        # Error injection control (for m_axi_slave responses)
        self.inject_resp_errors = False
        self.resp_error_rate = 0.0
        self.inject_aw_timeouts = False
        self.aw_timeout_rate = 0.0
        self.inject_w_timeouts = False
        self.w_timeout_rate = 0.0
        self.inject_b_timeouts = False
        self.b_timeout_rate = 0.0

        # Timeout task handle
        self.timeout_task = None

        # Verification data
        self.total_errors = 0

    def _create_randomizers(self):
        """Create timing randomizers for different test scenarios."""
        randomizers = {}

        fixed = 2

        # AW channel randomizers for s_axi interface
        randomizers['aw_always_ready'] = FlexRandomizer({
            'valid_delay': ([[0, 0]], [1.0])
        })

        randomizers['aw_fixed'] = FlexRandomizer({
            'valid_delay': ([[fixed, fixed]], [1.0])
        })

        randomizers['aw_fast'] = FlexRandomizer({
            'valid_delay': ([[0, 0], [1, 3]], [0.8, 0.2])
        })

        randomizers['aw_slow'] = FlexRandomizer({
            'valid_delay': ([[0, 0], [1, 10], [11, 20]], [0.2, 0.5, 0.3])
        })

        # W channel randomizers for s_axi interface
        randomizers['w_always_ready'] = FlexRandomizer({
            'valid_delay': ([[0, 0]], [1.0])
        })

        randomizers['w_fixed'] = FlexRandomizer({
            'valid_delay': ([[fixed, fixed]], [1.0])
        })

        randomizers['w_fast'] = FlexRandomizer({
            'valid_delay': ([[0, 0], [1, 3]], [0.8, 0.2])
        })

        randomizers['w_slow'] = FlexRandomizer({
            'valid_delay': ([[0, 0], [1, 10], [11, 20]], [0.2, 0.5, 0.3])
        })

        # B channel randomizers for m_axi interface
        randomizers['b_always_ready'] = FlexRandomizer({
            'ready_delay': ([[0, 0]], [1.0])
        })

        randomizers['b_fixed'] = FlexRandomizer({
            'ready_delay': ([[fixed, fixed]], [1.0])
        })

        randomizers['b_fast'] = FlexRandomizer({
            'ready_delay': ([[0, 0], [1, 3]], [0.8, 0.2])
        })

        randomizers['b_slow'] = FlexRandomizer({
            'ready_delay': ([[0, 0], [1, 10], [11, 20]], [0.2, 0.5, 0.3])
        })

        # Special randomizers for timeout testing
        # AW timeout testing - delays longer than timeout
        randomizers['aw_timeout'] = FlexRandomizer({
            'valid_delay': ([[0, 0], [self.timeout_aw, self.timeout_aw * 2]], [0.2, 0.8])
        })

        # W timeout testing - delays longer than timeout
        randomizers['w_timeout'] = FlexRandomizer({
            'valid_delay': ([[0, 0], [self.timeout_w, self.timeout_w * 2]], [0.2, 0.8])
        })

        # B timeout testing - delays longer than timeout
        randomizers['b_timeout'] = FlexRandomizer({
            'ready_delay': ([[0, 0], [self.timeout_b, self.timeout_b * 2]], [0.2, 0.8])
        })

        return randomizers

    def _initialize_memory(self):
        """Initialize the memory model with a pattern."""
        # Use a simple pattern: address + 0xA5A5A5A5
        for addr in range(0, 32768 * self.strb_width, self.strb_width):
            value = (addr + 0xA5A5A5A5) & ((1 << (8 * self.strb_width)) - 1)
            data_bytes = self.memory_model.integer_to_bytearray(value, self.strb_width)
            self.memory_model.write(addr, data_bytes, 0xFF)  # All bytes enabled

        self.log.info(f"Memory initialized with pattern: addr + 0xA5A5A5A5")

    def _handle_s_axi_write(self, id_value, transaction):
        """
        Handle a write transaction from the slave AXI interface.

        Args:
            id_value: Transaction ID
            transaction: Transaction information
        """
        if id_value in self.pending_writes:
            self.pending_writes[id_value]['monitor_detected'] = True
            self.log.debug(f"Detected write request on s_axi interface: ID={id_value:X}, addr=0x{transaction['aw_transaction'].awaddr:08X}")

    def _handle_m_axi_write(self, id_value, transaction):
        """
        Handle a write transaction from the master AXI interface.

        Args:
            id_value: Transaction ID
            transaction: Transaction information
        """
        # Store AW transactions for later verification
        if 'aw_transaction' in transaction:
            self.m_axi_aw_transactions.append(transaction['aw_transaction'])
            self.log.debug(f"Detected write address on m_axi interface: ID={id_value:X}, addr=0x{transaction['aw_transaction'].awaddr:08X}")

        # Store W transactions for later verification
        if 'w_transactions' in transaction:
            for w_tx in transaction['w_transactions']:
                self.m_axi_w_transactions.append(w_tx)
                if hasattr(w_tx, 'wlast') and w_tx.wlast:
                    self.log.debug(f"Detected write data (WLAST) on m_axi interface: ID={id_value:X}")

        # Check for completed transactions
        if 'complete' in transaction and transaction['complete']:
            matching_id = next(
                (
                    pending_id
                    for pending_id, pending_tx in self.pending_writes.items()
                    if id_value == pending_tx.get('m_axi_id')
                ),
                None,
            )
            if matching_id is not None:
                # Mark as m_axi complete and copy response
                self.pending_writes[matching_id]['m_axi_complete'] = True
                if 'b_transaction' in transaction:
                    self.pending_writes[matching_id]['b_transaction'] = transaction['b_transaction']

                # Check if fully complete (both s_axi and m_axi)
                if self.pending_writes[matching_id].get('s_axi_complete', False):
                    completed_tx = self.pending_writes.pop(matching_id)
                    self.completed_writes[matching_id] = completed_tx
                    self.log.info(f"Write transaction completed: ID={matching_id:X}, " +
                                f"addr=0x{completed_tx['addr']:08X}, " +
                                f"resp={completed_tx['b_transaction'].bresp}")

    def _get_next_id(self):
        """
        Get the next available transaction ID.

        Returns:
            Next available ID value
        """
        id_value = self.next_id
        self.next_id = (self.next_id + 1) % (1 << self.id_width)
        return id_value

    async def reset_interfaces(self):
        """Reset the AXI4 interfaces."""
        # Stop command handler if running
        if self.cmd_handler:
            await self.cmd_handler.stop()

        # Reset the AXI components
        await self.s_axi_master.reset_bus()
        await self.m_axi_slave.reset_bus()

        # Clear tracking data
        self.pending_writes.clear()
        self.completed_writes.clear()
        self.m_axi_aw_transactions.clear()
        self.m_axi_w_transactions.clear()

        # Reset ID counter
        self.next_id = 0

        # Reset error injection
        self.inject_resp_errors = False
        self.resp_error_rate = 0.0
        self.inject_aw_timeouts = False
        self.aw_timeout_rate = 0.0
        self.inject_w_timeouts = False
        self.w_timeout_rate = 0.0
        self.inject_b_timeouts = False
        self.b_timeout_rate = 0.0

        # Stop timeout task if running
        if self.timeout_task:
            self.timeout_task.kill()
            self.timeout_task = None

        # Reset verification data
        self.total_errors = 0

        # Start command handler if running
        if self.cmd_handler:
            await self.cmd_handler.start()

        self.log.info("AXI4 interfaces reset")

    def set_s_axi_aw_timing(self, mode):
        """
        Set the timing mode for the slave AXI AW channel.

        Args:
            mode: One of 'fixed', 'always_ready', 'fast', 'slow'
        """
        randomizer_key = f'aw_{mode}'
        if randomizer_key in self.randomizers:
            self.s_axi_master.aw_master.set_randomizer(self.randomizers[randomizer_key])
            self.log.info(f"S_AXI AW channel timing set to {mode}")
        else:
            self.log.error(f"Unknown AW timing mode: {mode}")

    def set_s_axi_w_timing(self, mode):
        """
        Set the timing mode for the slave AXI W channel.

        Args:
            mode: One of 'fixed', 'always_ready', 'fast', 'slow'
        """
        randomizer_key = f'w_{mode}'
        if randomizer_key in self.randomizers:
            self.s_axi_master.w_master.set_randomizer(self.randomizers[randomizer_key])
            self.log.info(f"S_AXI W channel timing set to {mode}")
        else:
            self.log.error(f"Unknown W timing mode: {mode}")

    def set_m_axi_b_timing(self, mode):
        """
        Set the timing mode for the master AXI B channel.

        Args:
            mode: One of 'always_ready', 'fast', 'slow', 'timeout'
        """
        randomizer_key = f'b_{mode}'
        if randomizer_key in self.randomizers:
            self.m_axi_slave.b_master.set_randomizer(self.randomizers[randomizer_key])
            self.log.info(f"M_AXI B channel timing set to {mode}")
        else:
            self.log.error(f"Unknown B timing mode: {mode}")

    async def send_write(self, addr, data, length=0, id_value=None, strb=None, busy_send=False):
        """
        Send a write transaction to the DUT.

        Args:
            addr: Address to write to
            data: Data to write (integer for single beat, list for burst)
            length: Burst length (0=1 beat, 1=2 beats, etc.)
            id_value: Optional specific ID to use (None for auto-generated)
            strb: Write strobe (byte enable)
            busy_send: If True, wait for transaction to complete before returning

        Returns:
            ID of the transaction or None if transaction validation failed
        """
        func_title = 'Axi4MasterWrAxi4Intf(send_write): '

        # === AXI4 Protocol Validation ===
        # Validate burst length
        if length > 255:
            self.log.warning(f"{func_title}Invalid burst length ({length}). AXI4 supports max 256 beats (0-255). Truncating to 255.")
            length = 255

        # Validate ID width
        if id_value is not None and id_value >= (1 << self.id_width):
            self.log.warning(f"{func_title}ID value 0x{id_value:X} exceeds ID width ({self.id_width} bits). Masking ID.")
            id_value = id_value & ((1 << self.id_width) - 1)

        # Calculate required address alignment based on size
        bytes_per_beat = 1 << self.dsize
        required_alignment = bytes_per_beat - 1
        aligned_addr = addr & ~required_alignment

        if aligned_addr != addr:
            self.log.warning(f"{func_title}Address 0x{addr:08X} not aligned to transfer size ({bytes_per_beat} bytes). Adjusting to 0x{aligned_addr:08X}")

        # Check for alignment boundary crossing
        if hasattr(self.dut, 'alignment_mask') and self.dut.alignment_mask.value.is_resolvable:
            alignment_mask = int(self.dut.alignment_mask.value)
            boundary_size = alignment_mask + 1

            # Calculate if transaction crosses an alignment boundary
            last_byte_addr = aligned_addr + (bytes_per_beat * (length + 1)) - 1
            start_segment = aligned_addr // boundary_size
            end_segment = last_byte_addr // boundary_size

            if start_segment != end_segment:
                boundaries_crossed = end_segment - start_segment
                next_boundary = (start_segment + 1) * boundary_size

                self.log.debug(f"{func_title}Transaction will cross {boundaries_crossed} alignment boundary(ies). "
                            f"First at 0x{next_boundary:08X}. Current alignment_mask=0x{alignment_mask:X}")
        else:
            self.log.debug(f"{func_title}alignmen_mask is not found or not resolvable")

        # Handle single-value data by converting to list
        if isinstance(data, int):
            data = [data] * (length + 1)

        # Validate data list length against burst length
        if len(data) < length + 1:
            self.log.warning(f"{func_title}Data list length ({len(data)}) is less than burst length ({length+1}). Padding with zeros.")
            # Pad with zeros if data list is too short
            data = data + [0] * (length + 1 - len(data))
        elif len(data) > length + 1:
            self.log.warning(f"{func_title}Data list length ({len(data)}) is greater than burst length ({length+1}). Truncating.")
            # Truncate if data list is too long
            data = data[:length + 1]

        # Check for AXI 4KB boundary crossing (still report as warning but don't fix)
        last_byte_addr = aligned_addr + (bytes_per_beat * (length + 1)) - 1
        start_4k = aligned_addr >> 12
        end_4k = last_byte_addr >> 12

        if start_4k != end_4k:
            self.log.warning(f"{func_title}Transaction crosses AXI 4KB boundary (0x{(start_4k+1)<<12:08X}). This may cause issues with some AXI slaves.")

        # Validate and generate strobe if not provided
        if strb is None:
            strb = (1 << self.strb_width) - 1  # All bytes enabled
        elif strb >= (1 << self.strb_width):
            self.log.warning(f"{func_title}Strobe value 0x{strb:X} exceeds width ({self.strb_width} bits). Masking strobe.")
            strb = strb & ((1 << self.strb_width) - 1)

        # Generate ID if not provided
        if id_value is None:
            id_value = self._get_next_id()

        # Create AW packet
        aw_packet = AXI4Packet.create_aw_packet(
            awid=id_value,
            awaddr=aligned_addr,
            awlen=length,
            awsize=self.dsize,
            awburst=self.burst,
            awlock=0,
            awcache=0,
            awprot=0,
            awqos=0,
            awregion=0,
            awuser=0
        )

        # Create W packets
        w_packets = []
        for i, beat_data in enumerate(data):
            w_packet = AXI4Packet.create_w_packet(
                wdata=beat_data,
                wstrb=strb,
                wlast=1 if i == length else 0,
                wuser=0
            )
            w_packets.append(w_packet)

        # Track in pending writes
        self.pending_writes[id_value] = {
            'addr': aligned_addr,
            'data': data,
            'length': length,
            'size': self.dsize,
            'burst': self.burst,
            'm_axi_id': id_value,  # Same ID used for now
            'start_time': cocotb.utils.get_sim_time('ns'),
            'monitor_detected': False,
            's_axi_complete': False,
            'm_axi_complete': False
        }

        # Send the AW packet
        if not busy_send:
            await self.s_axi_master.aw_master.send(aw_packet)
        else:
            await self.s_axi_master.aw_master.busy_send(aw_packet)

        # Send the W packets
        for w_packet in w_packets:
            if not busy_send:
                await self.s_axi_master.w_master.send(w_packet)
            else:
                await self.s_axi_master.w_master.busy_send(w_packet)

        self.log.info(f"{func_title}ID={id_value:X}, addr=0x{aligned_addr:08X}, length={length}")

        return id_value

    async def wait_for_write_complete(self, id_value, timeout_ns=None):
        """
        Wait for a write transaction to complete.

        Args:
            id_value: Transaction ID to wait for
            timeout_ns: Optional timeout in nanoseconds

        Returns:
            Dict with transaction data or None if timeout
        """
        start_time = cocotb.utils.get_sim_time('ns')

        while id_value not in self.completed_writes:
            # Check if transaction exists
            if id_value not in self.pending_writes:
                self.log.error(f"No pending write transaction with ID={id_value:X}")
                return None

            # Check for timeout
            if timeout_ns is not None:
                current_time = cocotb.utils.get_sim_time('ns')
                if current_time - start_time > timeout_ns:
                    self.log.warning(f"Timeout waiting for write transaction ID={id_value:X}")
                    return None

            # Wait and check again
            await Timer(100, units='ns')

        # Return the completed transaction
        return self.completed_writes[id_value]

    def set_dut_alignment_mask(self, value):
        """
        Set the alignment mask on the DUT.

        Args:
            value: Alignment mask value (typically a power of 2)
        """
        boundary = value & self.boundary_4k
        if hasattr(self.dut, 'alignment_mask'):
            self.dut.alignment_mask.value = boundary
            self.log.info(f"DUT alignment boundary set to {value}")
        else:
            self.log.error("DUT does not have alignment_mask signal")

    def configure_error_injection(self, error_type, enable, rate=0.0):
        """
        Configure error injection for testing error handling.

        Args:
            error_type: Type of error to inject ('resp', 'aw_timeout', 'w_timeout', 'b_timeout')
            enable: True to enable, False to disable
            rate: Error injection rate (0.0-1.0)
        """
        if error_type == 'resp':
            self.inject_resp_errors = enable
            self.resp_error_rate = rate
            self.log.info(f"Response error injection {'enabled' if enable else 'disabled'}, rate={rate}")
        elif error_type == 'aw_timeout':
            self.inject_aw_timeouts = enable
            self.aw_timeout_rate = rate
            self.log.info(f"AW timeout injection {'enabled' if enable else 'disabled'}, rate={rate}")
        elif error_type == 'w_timeout':
            self.inject_w_timeouts = enable
            self.w_timeout_rate = rate
            self.log.info(f"W timeout injection {'enabled' if enable else 'disabled'}, rate={rate}")
        elif error_type == 'b_timeout':
            self.inject_b_timeouts = enable
            self.b_timeout_rate = rate
            self.log.info(f"B timeout injection {'enabled' if enable else 'disabled'}, rate={rate}")
        else:
            self.log.error(f"Unknown error type: {error_type}")

    async def start_error_injection(self):
        """Start the error injection process based on configured settings."""
        if self.timeout_task is not None:
            self.timeout_task.kill()

        self.timeout_task = cocotb.start_soon(self._error_injection_task())
        self.log.info("Error injection task started")

    async def _error_injection_task(self):
        """Background task for injecting errors according to configured rates."""
        try:
            while True:
                # Inject response errors
                if self.inject_resp_errors and random.random() < self.resp_error_rate:
                    for id_value in self.pending_writes:
                        # Set SLVERR (2) or DECERR (3) in B response
                        self.m_axi_slave.b_master.field_config['bresp']['default'] = random.choice([2, 3])
                        self.log.info(f"Injected B response error for ID={id_value}")
                        break

                # Inject AW timeouts by manipulating awready signal
                if self.inject_aw_timeouts and random.random() < self.aw_timeout_rate and (self.m_axi_slave.aw_slave.valid_sig.value == 1 and self.m_axi_slave.aw_slave.ready_sig.value == 0):
                    self.m_axi_slave.aw_slave.ready_sig.value = 0
                    self.log.info("Injecting AW timeout")
                    await Timer(self.timeout_aw * 15, units='ns')  # Hold for longer than timeout

                # Inject W timeouts by manipulating wready signal
                if self.inject_w_timeouts and random.random() < self.w_timeout_rate and (self.m_axi_slave.w_slave.valid_sig.value == 1 and self.m_axi_slave.w_slave.ready_sig.value == 0):
                    self.m_axi_slave.w_slave.ready_sig.value = 0
                    self.log.info("Injecting W timeout")
                    await Timer(self.timeout_w * 15, units='ns')  # Hold for longer than timeout

                # Inject B timeouts by manipulating bvalid signal
                if self.inject_b_timeouts and random.random() < self.b_timeout_rate:
                    for id_value in self.pending_writes:
                        if 'b_transaction' not in self.pending_writes[id_value]:
                            # Temporarily disable B channel
                            prev_randomizer = self.m_axi_slave.b_master.randomizer
                            self.m_axi_slave.b_master.set_randomizer(self.randomizers['b_timeout'])
                            self.log.info(f"Injecting B timeout for ID={id_value}")
                            await Timer(self.timeout_b * 15, units='ns')  # Hold for longer than timeout
                            # Restore original randomizer
                            self.m_axi_slave.b_master.set_randomizer(prev_randomizer)
                            break

                # Wait before checking again
                await Timer(1000, units='ns')

        except cocotb.exceptions.SimTimeoutError:
            self.log.info("Error injection task stopped due to timeout")
        except Exception as e:
            self.log.error(f"Error in error injection task: {str(e)}")

    def verify_write_data(self, id_value):
        """
        Verify that the written data matches the expected pattern in memory.

        Args:
            id_value: Transaction ID to verify

        Returns:
            True if data matches expected pattern, False otherwise
        """
        if id_value not in self.completed_writes:
            self.log.error(f"No completed write transaction with ID={id_value:X}")
            return False

        transaction = self.completed_writes[id_value]
        addr = transaction['addr']
        data = transaction['data']
        size = transaction['size']
        bytes_per_beat = 1 << size

        # Verify each data beat was written correctly
        for i, expected_data in enumerate(data):
            # Calculate address for this beat
            if transaction['burst'] == 1 or transaction['burst'] != 0:  # INCR
                beat_addr = addr + (i * bytes_per_beat)
            else:  # FIXED
                beat_addr = addr
            # Get actual data from memory model
            actual_bytes = self.memory_model.read(beat_addr, bytes_per_beat)
            actual_data = self.memory_model.bytearray_to_integer(actual_bytes)

            # Compare
            if actual_data != expected_data:
                self.log.error(f"Data mismatch at beat {i}: expected=0x{expected_data:X}, actual=0x{actual_data:X}")
                self.total_errors += 1
                return False

        self.log.info(f"Write data verified for ID={id_value:X}: {len(data)} beats match expected pattern")
        return True

    async def verify_timeout_behavior(self, timeout_type, addr, data, length=0, size=2, burst=1, id_value=None):
        """
        Verify that timeout behavior works as expected.

        Args:
            timeout_type: Type of timeout to test ('aw', 'w', 'b')
            addr: Address to write to
            data: Data to write
            length: Burst length
            size: Transfer size
            burst: Burst type
            id_value: Optional specific ID to use

        Returns:
            True if timeout behavior is correct, False otherwise
        """
        # Set appropriate timeout mode
        if timeout_type == 'aw':
            self.set_m_axi_b_timing('fast')  # Fast B responses
            self.configure_error_injection('aw_timeout', True, 1.0)  # Always inject AW timeouts
        elif timeout_type == 'w':
            self.set_m_axi_b_timing('fast')  # Fast B responses
            self.configure_error_injection('w_timeout', True, 1.0)  # Always inject W timeouts
        else:  # 'b'
            self.set_m_axi_b_timing('timeout')  # Slow B responses to trigger timeout

        # Start error injection
        await self.start_error_injection()

        # Send write request
        tx_id = await self.send_write(addr, data, length, id_value)

        # Wait for reasonable time (longer than timeout)
        timeout_val = getattr(self, f'timeout_{timeout_type}')
        await Timer(timeout_val * 20, units='ns')

        # Verify that transaction didn't complete normally
        if tx_id in self.completed_writes:
            self.log.error(f"Transaction completed despite {timeout_type} timeout injection")
            self.total_errors += 1
            return False

        self.log.info(f"{timeout_type.upper()} timeout behavior verified: Transaction ID={tx_id:X} not completed")
        return True

    async def verify_split_transactions(self, alignment_mask, addr, data, length, size=2, burst=1, id_value=None):
        """
        Verify that transactions split correctly at alignment boundaries.

        Args:
            alignment_mask: Alignment mask to set on DUT
            addr: Address to write to
            data: Data to write
            length: Burst length
            size: Transfer size
            burst: Burst type
            id_value: Optional specific ID to use

        Returns:
            Tuple of (success, cnt)
        """
        # Set alignment mask on DUT
        self.set_dut_alignment_mask(alignment_mask)

        # Set fast timing for clean test
        self.set_s_axi_aw_timing('fast')
        self.set_s_axi_w_timing('fast')
        self.set_m_axi_b_timing('fast')

        # Clear previous transactions
        self.m_axi_aw_transactions.clear()

        # Send write request
        tx_id = await self.send_write(addr, data, length, id_value)

        # Wait for transaction to complete
        transaction = await self.wait_for_write_complete(tx_id, 1000000)  # 1ms timeout

        if transaction is None:
            self.log.error(f"Transaction ID={tx_id:X} did not complete")
            self.total_errors += 1
            return False, 0

        # Count splits by looking at AW transactions on m_axi interface
        cnt = len(self.m_axi_aw_transactions)

        # Calculate expected splits
        bytes_per_beat = 1 << size
        total_bytes = bytes_per_beat * (length + 1)
        end_addr = addr + total_bytes - 1

        # Calculate boundaries crossed
        boundaries_crossed = (end_addr // alignment_mask) - (addr // alignment_mask)
        expected_splits = 1 + boundaries_crossed

        if cnt != expected_splits:
            self.log.error(f"Split count mismatch: expected={expected_splits}, actual={cnt}")
            self.total_errors += 1
            return False, cnt

        # Verify data for additional check
        data_correct = self.verify_write_data(tx_id)

        self.log.info(f"Split transactions verified: ID={tx_id:X}, addr=0x{addr:08X}, splits={cnt}")
        return data_correct, cnt

    def get_transaction_status(self, id_value):
        """
        Get the status of a transaction.

        Args:
            id_value: Transaction ID

        Returns:
            Dict with transaction status or None if not found
        """
        if id_value in self.completed_writes:
            return {
                'state': 'completed',
                'data': self.completed_writes[id_value]
            }
        elif id_value in self.pending_writes:
            return {
                'state': 'pending',
                'data': self.pending_writes[id_value]
            }
        else:
            return None

    async def start_command_handler(self):
        """Start the AXI4 write command handler."""
        if not self.cmd_handler:
            from CocoTBFramework.components.axi4.axi4_command_handlers import AXI4WriteCommandHandler
            self.cmd_handler = AXI4WriteCommandHandler(
                aw_slave=self.m_axi_slave.aw_slave,
                w_slave=self.m_axi_slave.w_slave,
                b_master=self.m_axi_slave.b_master,
                memory_model=self.memory_model,
                log=self.log
            )

        await self.cmd_handler.start()
        self.log.info("Started AXI4 write command handler")

    async def stop_command_handler(self):
        """Stop the AXI4 write command handler."""
        if self.cmd_handler:
            await self.cmd_handler.stop()
            self.log.info("Stopped AXI4 write command handler")
