"""CDC Handshake Testbench using GAXI components"""
import os
import random
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_factories import (
    create_gaxi_master, create_gaxi_slave, create_gaxi_monitor
)


class CDCHandshakeTB(TBBase):
    """
    Testbench for Clock Domain Crossing (CDC) handshake module.
    Uses GAXI components to test the CDC handshake functionality
    with fields for pwrite, paddr, pwdata, pstrb, and pprot.
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        TBBase.__init__(self, dut)

        # Get test parameters from environment variables
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic')
        self.clk_src_PERIOD_NS = self.convert_to_int(os.environ.get('clk_src_PERIOD_NS', '50'))
        self.clk_dst_PERIOD_NS = self.convert_to_int(os.environ.get('clk_dst_PERIOD_NS', '10'))
        # Calculate clock frequencies in MHz
        self.clk_src_FREQ_MHZ = 1000 / self.clk_src_PERIOD_NS
        self.clk_dst_FREQ_MHZ = 1000 / self.clk_dst_PERIOD_NS

        # Test completion flag and stats
        self.done = False
        self.total_errors = 0
        self.num_line = 32768  # Memory size

        # Create a shared memory model for verification
        self.mem = MemoryModel(num_lines=self.num_line, bytes_per_line=self.STRB_WIDTH, log=self.log)

        # Define field configuration for the CDC handshake
        self.field_config = FieldConfig()
        self.field_config.add_field_dict('pwrite', {
            'bits': 1,
            'default': 0,
            'format': 'bin',
            'display_width': 1,
            'active_bits': (0, 0),
            'description': 'Write enable'
        })
        self.field_config.add_field_dict('paddr', {
            'bits': self.ADDR_WIDTH,
            'default': 0,
            'format': 'hex',
            'display_width': 8,
            'active_bits': (self.ADDR_WIDTH-1, 0),
            'description': 'Address'
        })
        self.field_config.add_field_dict('pwdata', {
            'bits': self.DATA_WIDTH,
            'default': 0,
            'format': 'hex',
            'display_width': 8,
            'active_bits': (self.DATA_WIDTH-1, 0),
            'description': 'Data'
        })
        self.field_config.add_field_dict('pstrb', {
            'bits': self.STRB_WIDTH,
            'default': 0xF,
            'format': 'bin',
            'display_width': 4,
            'active_bits': (self.STRB_WIDTH-1, 0),
            'description': 'Byte strobe'
        })
        self.field_config.add_field_dict('pprot', {
            'bits': 3,
            'default': 0,
            'format': 'bin',
            'display_width': 3,
            'active_bits': (2, 0),
            'description': 'Protection bits'
        })

        # Set up randomizers
        self.master_randomizer = FlexRandomizer({
            'valid_delay': ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
        })

        self.slave_randomizer = FlexRandomizer({
            'ready_delay': ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
        })

        master_signal_map = {
            'm2s_valid': 'valid_src',
            's2m_ready': 'ready_src'
        }
        master_optional_map = {
            'm2s_pkt': 'data_src',
        }
        # Create GAXI components for source domain
        self.src_master = create_gaxi_master(
            dut,
            'Source Master',
            '',
            dut.clk_src,
            signal_map=master_signal_map,
            optional_signal_map=master_optional_map,
            field_config=self.field_config,
            field_mode=True,
            randomizer=self.master_randomizer,
            log=self.log
        )

        self.src_monitor = create_gaxi_monitor(
            dut,
            'Source Monitor',
            '',
            dut.clk_src,
            signal_map=master_signal_map,
            optional_signal_map=master_optional_map,
            field_config=self.field_config,
            field_mode=True,
            is_slave=False,
            log=self.log
        )

        slave_signal_map = {
            'm2s_valid': 'valid_dst',
            's2m_ready': 'ready_dst'
        }
        slave_optional_map = {
            'm2s_pkt': 'data_dst',
        }
        # Create GAXI components for destination domain
        self.dst_slave = create_gaxi_slave(
            dut,
            'Destination Slave',
            '',
            dut.clk_dst,
            signal_map=slave_signal_map,
            optional_signal_map=slave_optional_map,
            field_config=self.field_config,
            field_mode=True,
            randomizer=self.slave_randomizer,
            log=self.log
        )

        self.dst_monitor = create_gaxi_monitor(
            dut,
            'Destination Monitor',
            '',
            dut.clk_dst,
            signal_map=slave_signal_map,
            optional_signal_map=slave_optional_map,
            field_config=self.field_config,
            field_mode=True,
            is_slave=True,
            log=self.log
        )

        # Create monitoring queues
        self.src_transactions = deque()
        self.dst_transactions = deque()

        # Add callbacks to store transactions
        self.src_monitor.add_callback(self.src_transaction_callback)
        self.dst_monitor.add_callback(self.dst_transaction_callback)

        # Log configuration
        self.log.info("CDC Handshake TB initialized with:")
        self.log.info(f"  ADDR_WIDTH: {self.ADDR_WIDTH}")
        self.log.info(f"  DATA_WIDTH: {self.DATA_WIDTH}")
        self.log.info(f"  STRB_WIDTH: {self.STRB_WIDTH}")
        self.log.info(f"  clk_src={self.clk_src_PERIOD_NS}ns ({self.clk_src_FREQ_MHZ:.1f}MHz)")
        self.log.info(f"  clk_dst={self.clk_dst_PERIOD_NS}ns ({self.clk_dst_FREQ_MHZ:.1f}MHz)")

    def src_transaction_callback(self, transaction):
        """Callback for source domain transactions"""
        self.src_transactions.append(transaction)

    def dst_transaction_callback(self, transaction):
        """Callback for destination domain transactions"""
        self.dst_transactions.append(transaction)

    async def reset_dut(self):
        """Reset the DUT and all components"""
        self.log.debug('Starting reset_dut')

        # Reset DUT control signals
        self.dut.rst_src_n.value = 0
        self.dut.rst_dst_n.value = 0

        # Reset BFM components
        await self.src_master.reset_bus()
        await self.dst_slave.reset_bus()

        # Hold reset for multiple cycles
        await self.wait_clocks('clk_src', 5)
        await self.wait_clocks('clk_dst', 5)

        # Release reset
        self.dut.rst_src_n.value = 1
        self.dut.rst_dst_n.value = 1

        # Wait for stabilization
        await self.wait_clocks('clk_src', 10)
        await self.wait_clocks('clk_dst', 10)

        # Clear monitoring queues
        self.src_transactions.clear()
        self.dst_transactions.clear()

        # Reset error counter
        self.total_errors = 0

        self.log.debug('Ending reset_dut')

    async def send_transaction(self, is_write, addr, data=None, strobe=None, prot=0):
        """
        Send a transaction through the CDC handshake.

        Args:
            is_write: True for write, False for read
            addr: Target address
            data: Data to write (for write transactions)
            strobe: Byte strobe (for write transactions)
            prot: Protection bits

        Returns:
            Transaction packet that was sent
        """
        start_time = get_sim_time('ns')

        # Create a packet with the specified fields
        packet = GAXIPacket(self.field_config)
        packet.pwrite = 1 if is_write else 0
        packet.paddr = addr

        # For write transactions, set data and strobe
        if is_write:
            # Use provided data or generate random value
            if data is None:
                data = random.randint(0, 2**self.DATA_WIDTH - 1)
            packet.pwdata = data

            # Use provided strobe or default to all bytes enabled
            if strobe is None:
                strobe = (2**self.STRB_WIDTH - 1)  # All bytes enabled
            packet.pstrb = strobe

            # Store write data in memory model for verification
            data_ba = self.mem.integer_to_bytearray(data, self.STRB_WIDTH)
            self.mem.write(addr, data_ba, strobe)
        else:
            # For read, set default values
            packet.pwdata = 0
            packet.pstrb = 0

        # Set protection bits
        packet.pprot = prot

        # Log transaction details
        self.log.info(f"Sending {('write' if is_write else 'read')} to addr 0x{addr:08X}" +
                    (f" with data 0x{packet.pwdata:08X} strobe 0x{packet.pstrb:X}" if is_write else ""))

        # Send transaction
        packet.start_time = start_time
        await self.src_master.send(packet)

        return packet

    async def wait_for_completion(self, timeout_cycles=10000):
        """
        Wait for all transactions to complete.

        Args:
            timeout_cycles: Maximum cycles to wait

        Returns:
            True if completed, False if timeout occurred
        """
        # Wait for source master to complete sending
        count = 0
        while self.src_master.transfer_busy and count < timeout_cycles:
            await self.wait_clocks('clk_src', 1)
            count += 1

        if count >= timeout_cycles:
            self.log.warning(f"Timeout waiting for src_master after {timeout_cycles} cycles")
            return False

        # Wait additional cycles for CDC crossing
        await self.wait_clocks('clk_src', 20)
        await self.wait_clocks('clk_dst', 20)

        return True

    def compare_transactions(self, expected_count=None):
        """
        Compare transactions between source and destination domains.

        Args:
            expected_count: Expected number of transactions (optional)

        Returns:
            True if all transactions matched, False otherwise
        """
        # Get transaction counts
        src_count = len(self.src_transactions)
        dst_count = len(self.dst_transactions)

        self.log.info(f"Comparing {src_count} source and {dst_count} destination transactions")

        # Check if expected count matches
        if expected_count is not None:
            if src_count != expected_count:
                self.log.error(f"Source transaction count mismatch: {src_count} vs {expected_count} expected")
                self.total_errors += 1

            if dst_count != expected_count:
                self.log.error(f"Destination transaction count mismatch: {dst_count} vs {expected_count} expected")
                self.total_errors += 1

        # Check if counts match between domains
        if src_count != dst_count:
            self.log.error(f"Transaction count mismatch: {src_count} source vs {dst_count} destination")
            self.total_errors += 1

        # Compare the minimum number of transactions from both domains
        min_count = min(src_count, dst_count)

        for i in range(min_count):
            src_trans = self.src_transactions[i]
            dst_trans = self.dst_transactions[i]

            # Compare fields
            fields_match = True
            mismatches = []

            for field in ['pwrite', 'paddr', 'pwdata', 'pstrb', 'pprot']:
                src_val = getattr(src_trans, field, None)
                dst_val = getattr(dst_trans, field, None)

                if src_val != dst_val:
                    fields_match = False
                    mismatches.append(f"{field}: {src_val} vs {dst_val}")

            if not fields_match:
                self.log.error(f"Transaction {i+1} field mismatch: " + ", ".join(mismatches))
                self.total_errors += 1

            # Verify that destination transaction occurred after source transaction
            if hasattr(src_trans, 'end_time') and hasattr(dst_trans, 'end_time') and dst_trans.end_time <= src_trans.end_time:
                self.log.error(f"Transaction {i+1} timing error: dst time {dst_trans.end_time}ns <= src time {src_trans.end_time}ns")
                self.total_errors += 1

        # Report the result
        if self.total_errors == 0:
            self.log.info(f"All {min_count} transactions verified successfully")
            return True
        else:
            self.log.error(f"Found {self.total_errors} transaction errors")
            return False

    async def run_basic_test(self, num_transactions=10):
        """
        Run a basic test with alternating reads and writes.

        Args:
            num_transactions: Number of transactions to test

        Returns:
            True if test passed, False otherwise
        """
        self.log.info(f"Starting basic test with {num_transactions} transactions")

        # Reset the DUT
        await self.reset_dut()

        # Send alternating read/write transactions
        base_addr = 0
        for i in range(num_transactions):
            is_write = (i % 2 == 0)  # Alternate write/read
            addr = base_addr + (i * 4)
            data = random.randint(0, 2**self.DATA_WIDTH - 1) if is_write else None
            strobe = 0xF if is_write else None

            await self.send_transaction(is_write, addr, data, strobe)

            # Add small delay between transactions
            await self.wait_clocks('clk_src', 5)

        # Wait for all transactions to complete
        await self.wait_for_completion()

        return self.compare_transactions(num_transactions)

    async def run_burst_test(self, num_transactions=20):
        """
        Run a burst test with multiple consecutive writes followed by reads.

        Args:
            num_transactions: Total number of transactions to test

        Returns:
            True if test passed, False otherwise
        """
        self.log.info(f"Starting burst test with {num_transactions} transactions")

        # Reset the DUT
        await self.reset_dut()

        # Set faster randomizers for bursts
        fast_randomizer = FlexRandomizer({
            'valid_delay': ([[0, 0]], [1]),  # No delay for bursts
        })
        self.src_master.set_randomizer(fast_randomizer)

        # First half: write transactions
        half = num_transactions // 2
        base_addr = 0

        # Send burst of writes
        for i in range(half):
            addr = base_addr + (i * 4)
            data = random.randint(0, 2**self.DATA_WIDTH - 1)

            await self.send_transaction(True, addr, data)

            # Minimal delay for bursts
            await self.wait_clocks('clk_src', 1)

        # Small delay between write and read bursts
        await self.wait_clocks('clk_src', 10)

        # Send burst of reads to same addresses
        for i in range(half):
            addr = base_addr + (i * 4)

            await self.send_transaction(False, addr)

            # Minimal delay for bursts
            await self.wait_clocks('clk_src', 1)

        # Wait for all transactions to complete
        await self.wait_for_completion()

        # Restore original randomizer
        self.src_master.set_randomizer(self.master_randomizer)

        return self.compare_transactions(num_transactions)

    async def run_random_test(self, num_transactions=50):
        """
        Run a test with random transaction patterns.

        Args:
            num_transactions: Number of transactions to test

        Returns:
            True if test passed, False otherwise
        """
        self.log.info(f"Starting random test with {num_transactions} transactions")

        # Reset the DUT
        await self.reset_dut()

        # Generate random transactions
        base_addr = 0
        for _ in range(num_transactions):
            # Random parameters
            is_write = random.choice([True, False])
            addr = base_addr + (random.randint(0, 63) * 4)  # Random address within range
            data = random.randint(0, 2**self.DATA_WIDTH - 1) if is_write else None

            # For writes, sometimes use partial strobes
            if is_write and random.random() < 0.3:  # 30% chance of partial strobe
                strobe = random.choice([0x1, 0x3, 0x7, 0xF, 0x5, 0xA, 0xC])
            else:
                strobe = 0xF if is_write else None

            # Random protection bits
            prot = random.randint(0, 7) if random.random() < 0.2 else 0  # 20% chance of non-zero prot

            await self.send_transaction(is_write, addr, data, strobe, prot)

            # Random delay between transactions
            delay = random.randint(1, 10)
            await self.wait_clocks('clk_src', delay)

        # Wait for all transactions to complete
        await self.wait_for_completion()

        return self.compare_transactions(num_transactions)
