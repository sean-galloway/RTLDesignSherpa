"""
AXI4 Master Read AXI4 Interface

This module provides a testbench interface for the AXI4 interfaces
of the AXI4 Master Read module, specifically focusing on the s_axi and m_axi
interfaces for read transactions.
"""

import cocotb
import random
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from collections import deque

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_master, create_axi4_slave, create_axi4_monitor
)
from CocoTBFramework.components.axi4.axi4_packets import AXI4Packet
from CocoTBFramework.components.axi4.axi4_command_handlers import AXI4ReadCommandHandler
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.memory_model import MemoryModel


class Axi4MasterRdAxi4Intf(TBBase):
    """
    Interface for the AXI4 interfaces of the AXI4 Master Read module.
    This class handles the slave and master AXI4 interfaces that carry
    the actual read requests and responses.
    """

    def __init__(self, dut, memory_model=None):
        """
        Initialize the AXI4 Master Read AXI4 Interface.

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
        channels = ['ar', 'r']

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
            randomizers={'ar': self.randomizers['ar_fast']},
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
            randomizers={'r': self.randomizers['r_fast']},
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
        self.s_axi_monitor.set_read_callback(self._handle_s_axi_read)
        self.m_axi_monitor.set_read_callback(self._handle_m_axi_read)

        # Create command handler to connect AR and R channels
        self.cmd_handler = AXI4ReadCommandHandler(
            ar_slave=self.m_axi_slave,
            r_master=self.m_axi_slave.r_master,
            memory_model=self.memory_model,
            log=self.log
        )

        # Transaction tracking
        self.pending_reads = {}  # Reads sent to DUT, awaiting response
        self.completed_reads = {}  # Completed read transactions
        self.m_axi_ar_transactions = []  # AR transactions on m_axi interface

        # ID counter for generating unique transaction IDs
        self.next_id = 0

        # Error injection control (for m_axi_slave responses)
        self.inject_resp_errors = False
        self.resp_error_rate = 0.0
        self.inject_ar_timeouts = False
        self.ar_timeout_rate = 0.0
        self.inject_r_timeouts = False
        self.r_timeout_rate = 0.0

        # Timeout task handle
        self.timeout_task = None

        # Verification data
        self.total_errors = 0

    def _create_randomizers(self):  # sourcery skip: merge-dict-assign
        """Create timing randomizers for different test scenarios."""
        randomizers = {}

        fixed = 2
    
        # AR channel randomizers for s_axi interface
        randomizers['ar_always_ready'] = FlexRandomizer({
            'valid_delay': ([[0, 0]], [1.0])
        })

        randomizers['ar_fixed'] = FlexRandomizer({
            'valid_delay': ([[fixed, fixed]], [1.0])
        })

        randomizers['ar_fast'] = FlexRandomizer({
            'valid_delay': ([[0, 0], [1, 3]], [0.8, 0.2])
        })

        randomizers['ar_slow'] = FlexRandomizer({
            'valid_delay': ([[0, 0], [1, 10], [11, 20]], [0.2, 0.5, 0.3])
        })

        # R channel randomizers for m_axi interface
        randomizers['r_always_ready'] = FlexRandomizer({
            'ready_delay': ([[0, 0]], [1.0])
        })

        randomizers['r_fixed'] = FlexRandomizer({
            'ready_delay': ([[fixed, fixed]], [1.0])
        })

        randomizers['r_fast'] = FlexRandomizer({
            'ready_delay': ([[0, 0], [1, 3]], [0.8, 0.2])
        })

        randomizers['r_slow'] = FlexRandomizer({
            'ready_delay': ([[0, 0], [1, 10], [11, 20]], [0.2, 0.5, 0.3])
        })

        # Special randomizers for timeout testing
        # AR timeout testing - delays longer than timeout
        randomizers['ar_timeout'] = FlexRandomizer({
            'valid_delay': ([[0, 0], [self.timeout_ar, self.timeout_ar * 2]], [0.2, 0.8])
        })

        # R timeout testing - delays longer than timeout
        randomizers['r_timeout'] = FlexRandomizer({
            'ready_delay': ([[0, 0], [self.timeout_r, self.timeout_r * 2]], [0.2, 0.8])
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

    def _handle_s_axi_read(self, id_value, transaction):
        """
        Handle a read transaction from the slave AXI interface.

        Args:
            id_value: Transaction ID
            transaction: Transaction information
        """
        if id_value in self.pending_reads:
            self.pending_reads[id_value]['monitor_detected'] = True
            self.log.debug(f"Detected read request on s_axi interface: ID={id_value:X}, addr=0x{transaction['ar_transaction'].araddr:08X}")

    def _handle_m_axi_read(self, id_value, transaction):
        """
        Handle a read transaction from the master AXI interface.

        Args:
            id_value: Transaction ID
            transaction: Transaction information
        """
        # Store AR transactions for later verification
        if 'ar_transaction' in transaction:
            self.m_axi_ar_transactions.append(transaction['ar_transaction'])
            self.log.debug(f"Detected read request on m_axi interface: ID={id_value:X}, addr=0x{transaction['ar_transaction'].araddr:08X}")

        # Check for completed transactions
        if 'complete' in transaction and transaction['complete']:
            matching_id = next(
                (
                    pending_id
                    for pending_id, pending_tx in self.pending_reads.items()
                    if id_value == pending_tx.get('m_axi_id')
                ),
                None,
            )
            if matching_id is not None:
                # Mark as m_axi complete and copy data
                self.pending_reads[matching_id]['m_axi_complete'] = True
                self.pending_reads[matching_id]['data'] = transaction.get('data', [])

                # Check if fully complete (both s_axi and m_axi)
                if self.pending_reads[matching_id].get('s_axi_complete', False):
                    completed_tx = self.pending_reads.pop(matching_id)
                    self.completed_reads[matching_id] = completed_tx
                    self.log.info(f"Read transaction completed: ID={matching_id:X}, addr=0x{completed_tx['addr']:08X}, beats={len(completed_tx['data'])}")

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
        self.pending_reads.clear()
        self.completed_reads.clear()
        self.m_axi_ar_transactions.clear()

        # Reset ID counter
        self.next_id = 0

        # Reset error injection
        self.inject_resp_errors = False
        self.resp_error_rate = 0.0
        self.inject_ar_timeouts = False
        self.ar_timeout_rate = 0.0
        self.inject_r_timeouts = False
        self.r_timeout_rate = 0.0

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

    def set_s_axi_ar_timing(self, mode):
        """
        Set the timing mode for the slave AXI AR channel.

        Args:
            mode: One of 'fixed', 'always_ready', 'fast', 'slow'
        """
        randomizer_key = f'ar_{mode}'
        if randomizer_key in self.randomizers:
            self.s_axi_master.ar_master.set_randomizer(self.randomizers[randomizer_key])
            self.log.info(f"S_AXI AR channel timing set to {mode}")
        else:
            self.log.error(f"Unknown AR timing mode: {mode}")

    def set_m_axi_r_timing(self, mode):
        """
        Set the timing mode for the master AXI R channel.

        Args:
            mode: One of 'always_ready', 'fast', 'slow', 'timeout'
        """
        randomizer_key = f'r_{mode}'
        if randomizer_key in self.randomizers:
            self.m_axi_slave.r_master.set_randomizer(self.randomizers[randomizer_key])
            self.log.info(f"M_AXI R channel timing set to {mode}")
        else:
            self.log.error(f"Unknown R timing mode: {mode}")

    async def send_read(self, addr, length=0, id_value=None, busy_send=False):
        """
        Send a read transaction to the DUT.

        Args:
            addr: Address to read from
            length: Burst length (0=1 beat, 1=2 beats, etc.)
            size: Transfer size (0=byte, 1=halfword, 2=word, 3=doubleword, etc.)
            burst: Burst type (0=FIXED, 1=INCR, 2=WRAP)
            id_value: Optional specific ID to use (None for auto-generated)

        Returns:
            ID of the transaction
        """
        func_title = 'Axi4MasterRdIdAxi4Intf(send_read): '
        # Generate ID if not provided
        if id_value is None:
            id_value = self._get_next_id()

        # Align address with data width
        bytes_per_beat = 1 << self.dsize
        aligned_addr = addr & ~(bytes_per_beat - 1)
        
        if aligned_addr != addr:
            self.log.info(f"{func_title}Aligning address 0x{addr:08X} to 0x{aligned_addr:08X} for size {self.dsize}")

        # Create packet for AXI4 master
        packet = AXI4Packet.create_ar_packet(
            arid=id_value,
            araddr=addr,
            arlen=length,
            arsize=self.dsize,
            arburst=self.burst
        )

        # Track in pending reads
        self.pending_reads[id_value] = {
            'addr': aligned_addr,
            'length': length,
            'size': self.dsize,
            'burst': self.burst,
            'm_axi_id': id_value,  # Same ID used for now
            'start_time': cocotb.utils.get_sim_time('ns'),
            'monitor_detected': False,
            's_axi_complete': False,
            'm_axi_complete': False
        }

        # Send the read request
        if not busy_send:
            await self.s_axi_master.ar_master.send(packet)
        else:
            await self.s_axi_master.ar_master.busy_send(packet)

        self.log.info(f"{func_title}ID={id_value:X}, addr=0x{aligned_addr:08X}, length={length}")

        return id_value

    async def wait_for_read_complete(self, id_value, timeout_ns=None):
        """
        Wait for a read transaction to complete.

        Args:
            id_value: Transaction ID to wait for
            timeout_ns: Optional timeout in nanoseconds

        Returns:
            Dict with transaction data or None if timeout
        """
        start_time = cocotb.utils.get_sim_time('ns')

        while id_value not in self.completed_reads:
            # Check if transaction exists
            if id_value not in self.pending_reads:
                self.log.error(f"No pending read transaction with ID={id_value:X}")
                return None

            # Check for timeout
            if timeout_ns is not None:
                current_time = cocotb.utils.get_sim_time('ns')
                if current_time - start_time > timeout_ns:
                    self.log.warning(f"Timeout waiting for read transaction ID={id_value:X}")
                    return None

            # Wait and check again
            await Timer(100, units='ns')

        # Return the completed transaction
        return self.completed_reads[id_value]

    def set_dut_alignment_boundary(self, value):
        """
        Set the alignment boundary on the DUT.

        Args:
            value: Alignment boundary value (typically a power of 2)
        """
        boundary = value & 4095
        if hasattr(self.dut, 'alignment_boundary'):
            self.dut.alignment_boundary.value = boundary
            self.log.info(f"DUT alignment boundary set to {value}")
        else:
            self.log.error("DUT does not have alignment_boundary signal")

    def configure_error_injection(self, error_type, enable, rate=0.0):
        """
        Configure error injection for testing error handling.

        Args:
            error_type: Type of error to inject ('resp', 'ar_timeout', 'r_timeout')
            enable: True to enable, False to disable
            rate: Error injection rate (0.0-1.0)
        """
        if error_type == 'resp':
            self.inject_resp_errors = enable
            self.resp_error_rate = rate
            self.log.info(f"Response error injection {'enabled' if enable else 'disabled'}, rate={rate}")
        elif error_type == 'ar_timeout':
            self.inject_ar_timeouts = enable
            self.ar_timeout_rate = rate
            self.log.info(f"AR timeout injection {'enabled' if enable else 'disabled'}, rate={rate}")
        elif error_type == 'r_timeout':
            self.inject_r_timeouts = enable
            self.r_timeout_rate = rate
            self.log.info(f"R timeout injection {'enabled' if enable else 'disabled'}, rate={rate}")
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
                    # Find a pending read on m_axi to inject error
                    for packet in self.m_axi_slave.ar_slave.received_queue:
                        # Modify the response field (if accessible)
                        if hasattr(packet, 'rresp'):
                            # Set to SLVERR (2) or DECERR (3)
                            packet.rresp = random.choice([2, 3])
                            self.log.info(f"Injected response error for ID={packet.rid}")
                            break

                # Inject AR timeouts by manipulating arready signal
                if self.inject_ar_timeouts and random.random() < self.ar_timeout_rate and (self.m_axi_slave.ar_slave.valid_sig.value == 1 and self.m_axi_slave.ar_slave.ready_sig.value == 0):
                    self.m_axi_slave.ar_slave.ready_sig.value = 0
                    self.log.info("Injecting AR timeout")
                    await Timer(self.timeout_ar * 15, units='ns')  # Hold for longer than timeout

                # Inject R timeouts by manipulating rready signal
                if self.inject_r_timeouts and random.random() < self.r_timeout_rate and (self.m_axi_slave.r_master.valid_sig.value == 1 and self.m_axi_slave.r_master.ready_sig.value == 0):
                    self.m_axi_slave.r_master.ready_sig.value = 0
                    self.log.info("Injecting R timeout")
                    await Timer(self.timeout_r * 15, units='ns')  # Hold for longer than timeout

                # Wait before checking again
                await Timer(1000, units='ns')

        except cocotb.exceptions.SimTimeoutError:
            self.log.info("Error injection task stopped due to timeout")
        except Exception as e:
            self.log.error(f"Error in error injection task: {str(e)}")

    def verify_response_data(self, id_value):
        """
        Verify that the response data matches the expected pattern in memory.

        Args:
            id_value: Transaction ID to verify

        Returns:
            True if data matches expected pattern, False otherwise
        """
        if id_value not in self.completed_reads:
            self.log.error(f"No completed read transaction with ID={id_value:X}")
            return False

        transaction = self.completed_reads[id_value]
        addr = transaction['addr']
        size = transaction['size']
        bytes_per_beat = 1 << size

        # Verify each data beat
        for i, data in enumerate(transaction['data']):
            # Calculate address for this beat
            if transaction['burst'] == 1 or transaction['burst'] != 0:  # INCR
                beat_addr = addr + (i * bytes_per_beat)
            else:  # FIXED
                beat_addr = addr
            # Get expected data from memory model
            expected_bytes = self.memory_model.read(beat_addr, bytes_per_beat)
            expected_data = self.memory_model.bytearray_to_integer(expected_bytes)

            # Compare
            if data != expected_data:
                self.log.error(f"Data mismatch at beat {i}: expected=0x{expected_data:X}, actual=0x{data:X}")
                self.total_errors += 1
                return False

        self.log.info(f"Response data verified for ID={id_value:X}: {len(transaction['data'])} beats match expected pattern")
        return True

    async def verify_timeout_behavior(self, timeout_type, addr, length=0, size=2, burst=1, id_value=None):
        """
        Verify that timeout behavior works as expected.

        Args:
            timeout_type: Type of timeout to test ('ar', 'r')
            addr: Address to read from
            length: Burst length
            size: Transfer size
            burst: Burst type
            id_value: Optional specific ID to use

        Returns:
            True if timeout behavior is correct, False otherwise
        """
        # Set appropriate timeout mode
        if timeout_type == 'ar':
            self.set_m_axi_r_timing('fast')  # Fast R responses
            self.configure_error_injection('ar_timeout', True, 1.0)  # Always inject AR timeouts
        else:  # 'r'
            self.set_m_axi_r_timing('timeout')  # Slow R responses to trigger timeout

        # Start error injection
        await self.start_error_injection()

        # Send read request
        tx_id = await self.send_read(addr, length, id_value)

        # Wait for reasonable time (longer than timeout)
        timeout_val = self.timeout_ar if timeout_type == 'ar' else self.timeout_r
        await Timer(timeout_val * 20, units='ns')

        # Verify that transaction didn't complete normally
        if tx_id in self.completed_reads:
            self.log.error(f"Transaction completed despite {timeout_type} timeout injection")
            self.total_errors += 1
            return False

        self.log.info(f"{timeout_type.upper()} timeout behavior verified: Transaction ID={tx_id:X} not completed")
        return True

    async def verify_split_transactions(self, alignment_boundary, addr, length, size=2, burst=1, id_value=None):
        """
        Verify that transactions split correctly at alignment boundaries.

        Args:
            alignment_boundary: Alignment boundary to set on DUT
            addr: Address to read from
            length: Burst length
            size: Transfer size
            burst: Burst type
            id_value: Optional specific ID to use

        Returns:
            Tuple of (success, num_splits)
        """
        # Set alignment boundary on DUT
        self.set_dut_alignment_boundary(alignment_boundary)

        # Set fast timing for clean test
        self.set_s_axi_ar_timing('fast')
        self.set_m_axi_r_timing('fast')

        # Clear previous transactions
        self.m_axi_ar_transactions.clear()

        # Send read request
        tx_id = await self.send_read(addr, length, id_value)

        # Wait for transaction to complete
        transaction = await self.wait_for_read_complete(tx_id, 1000000)  # 1ms timeout

        if transaction is None:
            self.log.error(f"Transaction ID={tx_id:X} did not complete")
            self.total_errors += 1
            return False, 0

        # Count splits by looking at AR transactions on m_axi interface
        num_splits = len(self.m_axi_ar_transactions)

        # Calculate expected splits
        bytes_per_beat = 1 << size
        total_bytes = bytes_per_beat * (length + 1)
        end_addr = addr + total_bytes - 1

        # Calculate boundaries crossed
        boundaries_crossed = (end_addr // alignment_boundary) - (addr // alignment_boundary)
        expected_splits = 1 + boundaries_crossed

        if num_splits != expected_splits:
            self.log.error(f"Split count mismatch: expected={expected_splits}, actual={num_splits}")
            self.total_errors += 1
            return False, num_splits

        # Verify data for additional check
        data_correct = self.verify_response_data(tx_id)

        self.log.info(f"Split transactions verified: ID={tx_id:X}, addr=0x{addr:08X}, splits={num_splits}")
        return data_correct, num_splits

    def get_transaction_status(self, id_value):
        """
        Get the status of a transaction.

        Args:
            id_value: Transaction ID

        Returns:
            Dict with transaction status or None if not found
        """
        if id_value in self.completed_reads:
            return {
                'state': 'completed',
                'data': self.completed_reads[id_value]
            }
        elif id_value in self.pending_reads:
            return {
                'state': 'pending',
                'data': self.pending_reads[id_value]
            }
        else:
            return None

    async def start_command_handler(self):
        """Start the AXI4 read command handler."""
        await self.cmd_handler.start()
        self.log.info("Started AXI4 read command handler")

    async def stop_command_handler(self):
        """Stop the AXI4 read command handler."""
        await self.cmd_handler.stop()
        self.log.info("Stopped AXI4 read command handler")
