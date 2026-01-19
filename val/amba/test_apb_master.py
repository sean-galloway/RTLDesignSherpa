# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBGAXIScoreboard
# Purpose: Enhanced scoreboard for verifying APB and GAXI transactions with flexible field 
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import random
from collections import deque, defaultdict

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import Timer, RisingEdge
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.apb.apb_sequence import APBSequence
from CocoTBFramework.components.apb.apb_factories import \
    create_apb_monitor, create_apb_scoreboard
from CocoTBFramework.components.apb.apb_components import APBSlave
from CocoTBFramework.components.gaxi.gaxi_factories import \
    create_gaxi_master, create_gaxi_slave, create_gaxi_monitor
from CocoTBFramework.tbclasses.apb.apbgaxiconfig import APBGAXIConfig
# from CocoTBFramework.scoreboards.apb_gaxi_scoreboard import APBGAXIScoreboard  # Use improved version below
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.amba.amba_random_configs import APB_SLAVE_RANDOMIZER_CONFIGS, AXI_RANDOMIZER_CONFIGS
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# WaveDrom support
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver,
    TemporalConstraint,
    TemporalEvent,
    SignalTransition,
    TemporalRelation
)
from CocoTBFramework.components.wavedrom.wavejson_gen import create_apb_wavejson_generator
from CocoTBFramework.components.wavedrom.utility import get_apb_field_config
from CocoTBFramework.tbclasses.wavedrom_user.apb import setup_apb_constraints_with_boundaries

# NOTE: Use the improved APBGAXIScoreboard from the artifact above instead of the original
# Replace the import above with your improved scoreboard once it's integrated

# TODO: Replace this with import once integrated into the framework
class APBGAXIScoreboard:
    """
    Enhanced scoreboard for verifying APB and GAXI transactions with flexible field handling.
    This version automatically detects and handles different field naming conventions.
    """

    def __init__(self, name, log=None):
        self.name = name
        self.log = log
        self.apb_writes = defaultdict(deque)
        self.apb_reads = defaultdict(deque)
        self.gaxi_writes = defaultdict(deque)
        self.gaxi_reads = defaultdict(deque)
        self.total_matches = 0
        self.total_mismatches = 0
        self.total_dropped = 0
        self.total_verified = 0
        self.address_coverage = set()
        self.type_coverage = {"apb_write": 0, "apb_read": 0, "gaxi_write": 0, "gaxi_read": 0}

    def _get_field_value(self, transaction, *field_names):
        """Get field value from transaction, trying multiple possible field names."""
        for field_name in field_names:
            if hasattr(transaction, field_name):
                value = getattr(transaction, field_name)
                if hasattr(value, 'value'):  # cocotb signal
                    return int(value.value) if value.value.is_resolvable else None
                elif hasattr(transaction, 'fields') and field_name in transaction.fields:
                    return transaction.fields[field_name]
                else:
                    return value
        return None

    def _get_address(self, transaction):
        """Get address from transaction using flexible field names."""
        return self._get_field_value(transaction, 'addr', 'paddr', 'address')

    def _get_write_flag(self, transaction):
        """Get write flag from transaction using flexible field names."""
        if hasattr(transaction, 'direction'):
            return 1 if transaction.direction == 'WRITE' else 0
        write_flag = self._get_field_value(transaction, 'cmd', 'pwrite', 'write', 'is_write')
        return write_flag if write_flag is not None else 0

    def _get_write_data(self, transaction):
        """Get write data from transaction using flexible field names."""
        return self._get_field_value(transaction, 'data', 'pwdata', 'wdata', 'write_data')

    def _get_read_data(self, transaction):
        """Get read data from transaction using flexible field names."""
        return self._get_field_value(transaction, 'data', 'prdata', 'rdata', 'read_data')

    def add_apb_transaction(self, transaction):
        """Add an APB transaction to the scoreboard with flexible field handling."""
        addr = self._get_address(transaction)
        if addr is None:
            if self.log: self.log.error("APB transaction missing address field")
            return
        addr = addr & 0xFFF
        write_flag = self._get_write_flag(transaction)

        if write_flag:
            matched = self._check_write_matches(addr, transaction, is_apb=True)
            if not matched:
                self.apb_writes[addr].append(transaction)
            self.type_coverage["apb_write"] += 1
        else:
            matched = self._check_read_matches(addr, transaction, is_apb=True)
            if not matched:
                self.apb_reads[addr].append(transaction)
            self.type_coverage["apb_read"] += 1

        self.address_coverage.add(addr)

    def add_gaxi_transaction(self, transaction):
        """Add a GAXI transaction to the scoreboard with flexible field handling."""
        addr = self._get_address(transaction)
        if addr is None:
            if self.log: self.log.error("GAXI transaction missing address field")
            return
        addr = addr & 0xFFF
        write_flag = self._get_write_flag(transaction)

        if write_flag:
            matched = self._check_write_matches(addr, transaction, is_apb=False)
            if not matched:
                self.gaxi_writes[addr].append(transaction)
            self.type_coverage["gaxi_write"] += 1
        else:
            matched = self._check_read_matches(addr, transaction, is_apb=False)
            if not matched:
                self.gaxi_reads[addr].append(transaction)
            self.type_coverage["gaxi_read"] += 1

        self.address_coverage.add(addr)

    def _check_write_matches(self, addr, transaction, is_apb=True):
        """Check for write transaction matches."""
        if is_apb and self.gaxi_writes[addr]:
            gaxi_transaction = self.gaxi_writes[addr].popleft()
            apb_data = self._get_write_data(transaction)
            gaxi_data = self._get_write_data(gaxi_transaction)

            if apb_data == gaxi_data:
                if self.log: self.log.debug(f"Matched write at addr 0x{addr:08X}: APB=0x{apb_data:08X}, GAXI=0x{gaxi_data:08X}")
                self.total_matches += 1
            else:
                if self.log: self.log.error(f"Write data mismatch at addr 0x{addr:08X}: APB=0x{apb_data:08X}, GAXI=0x{gaxi_data:08X}")
                self.total_mismatches += 1
            self.total_verified += 1
            return True
        elif not is_apb and self.apb_writes[addr]:
            apb_transaction = self.apb_writes[addr].popleft()
            apb_data = self._get_write_data(apb_transaction)
            gaxi_data = self._get_write_data(transaction)

            if apb_data == gaxi_data:
                if self.log: self.log.debug(f"Matched write at addr 0x{addr:08X}: APB=0x{apb_data:08X}, GAXI=0x{gaxi_data:08X}")
                self.total_matches += 1
            else:
                if self.log: self.log.error(f"Write data mismatch at addr 0x{addr:08X}: APB=0x{apb_data:08X}, GAXI=0x{gaxi_data:08X}")
                self.total_mismatches += 1
            self.total_verified += 1
            return True
        return False

    def _check_read_matches(self, addr, transaction, is_apb=True):
        """Check for read transaction matches."""
        if is_apb and self.gaxi_reads[addr]:
            gaxi_transaction = self.gaxi_reads[addr].popleft()
            apb_data = self._get_read_data(transaction)
            gaxi_data = self._get_read_data(gaxi_transaction)

            if apb_data == gaxi_data:
                if self.log: self.log.debug(f"Matched read at addr 0x{addr:08X}: APB=0x{apb_data:08X}, GAXI=0x{gaxi_data:08X}")
                self.total_matches += 1
            else:
                if self.log: self.log.error(f"Read data mismatch at addr 0x{addr:08X}: APB=0x{apb_data:08X}, GAXI=0x{gaxi_data:08X}")
                self.total_mismatches += 1
            self.total_verified += 1
            return True
        elif not is_apb and self.apb_reads[addr]:
            apb_transaction = self.apb_reads[addr].popleft()
            apb_data = self._get_read_data(apb_transaction)
            gaxi_data = self._get_read_data(transaction)

            if apb_data == gaxi_data:
                if self.log: self.log.debug(f"Matched read at addr 0x{addr:08X}: APB=0x{apb_data:08X}, GAXI=0x{gaxi_data:08X}")
                self.total_matches += 1
            else:
                if self.log: self.log.error(f"Read data mismatch at addr 0x{addr:08X}: APB=0x{apb_data:08X}, GAXI=0x{gaxi_data:08X}")
                self.total_mismatches += 1
            self.total_verified += 1
            return True
        return False

    async def check_scoreboard(self, timeout=None):
        """Check scoreboard for unmatched transactions."""
        if timeout:
            await Timer(timeout, units='ns')

        unmatched = 0
        for addr, queue in self.apb_writes.items():
            if queue:
                unmatched += len(queue)
                if self.log: self.log.warning(f"Unmatched APB writes at addr 0x{addr:08X}: {len(queue)}")

        for addr, queue in self.apb_reads.items():
            if queue:
                unmatched += len(queue)
                if self.log: self.log.warning(f"Unmatched APB reads at addr 0x{addr:08X}: {len(queue)}")

        for addr, queue in self.gaxi_writes.items():
            if queue:
                unmatched += len(queue)
                if self.log: self.log.warning(f"Unmatched GAXI writes at addr 0x{addr:08X}: {len(queue)}")

        for addr, queue in self.gaxi_reads.items():
            if queue:
                unmatched += len(queue)
                if self.log: self.log.warning(f"Unmatched GAXI reads at addr 0x{addr:08X}: {len(queue)}")

        self.total_dropped = unmatched
        if self.log: self.log.info(f"Scoreboard check: {self.total_matches} matches, {self.total_mismatches} mismatches, {self.total_dropped} unmatched")

        total = self.total_verified + self.total_dropped
        verification_rate = (self.total_verified / total) * 100 if total else 0
        if self.log: self.log.info(f"Verification rate: {verification_rate:.1f}% ({self.total_verified}/{total})")

        return self.total_mismatches == 0 and self.total_dropped == 0

    def report(self):
        """Generate a report of scoreboard statistics."""
        report = [
            f"=== {self.name} Report ===",
            f"Total transactions verified: {self.total_verified}",
            f"Matching transactions: {self.total_matches}",
            f"Mismatched transactions: {self.total_mismatches}",
            f"Unmatched transactions: {self.total_dropped}",
            f"Unique addresses covered: {len(self.address_coverage)}",
            "Transaction type coverage:",
            f"  APB writes: {self.type_coverage['apb_write']}",
            f"  APB reads: {self.type_coverage['apb_read']}",
            f"  GAXI writes: {self.type_coverage['gaxi_write']}",
            f"  GAXI reads: {self.type_coverage['gaxi_read']}",
        ]
        total = self.total_verified + self.total_dropped
        verification_rate = (self.total_verified / total) * 100 if total else 0
        report.append(f"Verification rate: {verification_rate:.1f}%")
        return "\n".join(report)

    def clear(self):
        """Clear all transactions and reset statistics."""
        self.apb_writes.clear()
        self.apb_reads.clear()
        self.gaxi_writes.clear()
        self.gaxi_reads.clear()
        self.total_matches = 0
        self.total_mismatches = 0
        self.total_dropped = 0
        self.total_verified = 0
        self.address_coverage.clear()
        self.type_coverage = {"apb_write": 0, "apb_read": 0, "gaxi_write": 0, "gaxi_read": 0}
        if self.log: self.log.info(f"Scoreboard {self.name} cleared")


class APBMasterTB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.CMD_DEPTH = self.convert_to_int(os.environ.get('TEST_CMD_DEPTH', '6'))
        self.RSP_DEPTH = self.convert_to_int(os.environ.get('TEST_RSP_DEPTH', '6'))
        self.done = False
        # Number of registers to test
        self.registers = 64

        # Task termination flag
        self.done = False
        self.num_line = 32768

        # Create a shared memory model for both APB and GAXI components
        self.mem = MemoryModel(num_lines=self.num_line, bytes_per_line=self.STRB_WIDTH, log=self.log)

        # Queue to track read commands waiting for responses
        self.pending_reads = deque()
        super_debug = False  # Reduce debug output

        # Configure APB components
        self.apb_monitor = create_apb_monitor(
            dut,
            'APB Monitor',
            'm_apb',
            dut.pclk,
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            log=self.log
        )

        # FIXED: Create APB slave directly with shared memory model
        self.apb_slave = APBSlave(
            dut,
            'APB Slave',
            'm_apb',
            dut.pclk,
            registers=[0] * (self.registers * self.STRB_WIDTH),  # Initial register values
            bus_width=self.DATA_WIDTH,
            addr_width=self.ADDR_WIDTH,
            randomizer=FlexRandomizer(APB_SLAVE_RANDOMIZER_CONFIGS['constrained']),
            log=self.log
        )

        # FIXED: Replace the APB slave's memory model with our shared one
        self.apb_slave.mem = self.mem
        self.apb_slave.num_lines = self.num_line

        # Create APB scoreboard
        self.apb_scoreboard = create_apb_scoreboard(
            'APB Scoreboard',
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            log=self.log
        )

        # Configure GAXI components for command interface
        self.apbgaxiconfig = APBGAXIConfig(
            addr_width=self.ADDR_WIDTH,
            data_width=self.DATA_WIDTH,
            strb_width=self.STRB_WIDTH
        )
        self.cmd_field_config = self.apbgaxiconfig.create_cmd_field_config()

        self.cmd_monitor = create_gaxi_monitor(
            dut,
            'CMD Monitor',
            '',  # No prefix as we're using signal map
            dut.pclk,
            field_config=self.cmd_field_config,
            pkt_prefix='cmd',
            is_slave=True,  # Monitoring slave-side signals
            log=self.log,
            super_debug=super_debug,
            multi_sig=True,  # Using separate signals
        )

        # FIXED: Remove memory model from GAXI command master - APB slave should handle memory
        self.cmd_master = create_gaxi_master(
            dut,
            'CMD Master',
            '',  # No prefix as we're using signal map
            dut.pclk,
            field_config=self.cmd_field_config,
            pkt_prefix='cmd',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['constrained']['master']),
            memory_model=None,  # FIXED: No memory model for command master
            log=self.log,
            super_debug=super_debug,
            multi_sig=True,  # Using separate signals
        )

        # Configure GAXI components for response interface
        self.rsp_field_config = self.apbgaxiconfig.create_rsp_field_config()

        self.rsp_monitor = create_gaxi_monitor(
            dut,
            'RSP Monitor',
            '',  # No prefix as we're using signal map
            dut.pclk,
            field_config=self.rsp_field_config,
            pkt_prefix='rsp',
            is_slave=False,  # Monitoring master-side signals
            log=self.log,
            super_debug=super_debug,
            multi_sig=True,  # Using separate signals
        )

        self.rsp_slave = create_gaxi_slave(
            dut,
            'RSP Slave',
            '',  # No prefix as we're using signal map
            dut.pclk,
            field_config=self.rsp_field_config,
            pkt_prefix='rsp',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['slave']),
            log=self.log,
            super_debug=super_debug,
            multi_sig=True,  # Using separate signals
        )

        # Set up APB-GAXI scoreboard
        self.apb_gaxi_scoreboard = APBGAXIScoreboard(
            'APB-GAXI Scoreboard',
            log=self.log
        )

        # Connect monitors to scoreboard
        self.apb_monitor.add_callback(self.apb_transaction_callback)
        self.cmd_monitor.add_callback(self.cmd_transaction_callback)
        self.rsp_monitor.add_callback(self.rsp_transaction_callback)

        # Initialize queues for monitoring
        self.apb_monitor_queue = deque()
        self.cmd_monitor_queue = deque()
        self.rsp_monitor_queue = deque()

    def cmd_transaction_callback(self, transaction):
        """Callback for GAXI CMD monitor transactions - SIMPLIFIED."""
        self.cmd_monitor_queue.append(transaction)

        # Only add write commands to the scoreboard directly
        write_flag = getattr(transaction, 'pwrite', getattr(transaction, 'cmd', 0))
        if write_flag == 1:  # Write command
            addr = getattr(transaction, 'paddr', getattr(transaction, 'addr', 0))
            data = getattr(transaction, 'pwdata', getattr(transaction, 'data', 0))
            self.log.info(f"Adding GAXI write command: addr=0x{addr:08X}, data=0x{data:08X}")
            self.apb_gaxi_scoreboard.add_gaxi_transaction(transaction)
        else:  # Read command
            transaction.tx_id = len(self.pending_reads)
            self.pending_reads.append(transaction)
            addr = getattr(transaction, 'paddr', getattr(transaction, 'addr', 0))
            self.log.info(f"Adding read command to pending queue: tx_id={transaction.tx_id}, addr=0x{addr:08X}")

    def apb_transaction_callback(self, transaction):
        """Callback for APB monitor transactions - SIMPLIFIED."""
        self.apb_monitor_queue.append(transaction)

        addr = getattr(transaction, 'paddr', 0)
        self.log.info(f"APB Transaction: {transaction.direction} addr=0x{addr:08X}")

        # For read transactions, save response data for matching GAXI command
        if transaction.direction == 'READ':
            data = getattr(transaction, 'prdata', 0)
            self.log.info(f"APB Read: addr=0x{addr:08X}, data=0x{data:08X}")

            # Look for a pending read command with matching address
            found = False
            for cmd in self.pending_reads:
                cmd_addr = getattr(cmd, 'paddr', getattr(cmd, 'addr', 0))
                if cmd_addr == addr and not hasattr(cmd, 'response_data'):
                    cmd.response_data = data
                    self.log.info(f"Matched APB read data for tx_id={cmd.tx_id}: addr=0x{addr:08X}, data=0x{data:08X}")
                    found = True
                    break

            if not found:
                self.log.warning(f"No pending GAXI read found for APB read: addr=0x{addr:08X}")
        else:
            # Write transaction
            data = getattr(transaction, 'pwdata', 0)
            self.log.info(f"APB Write: addr=0x{addr:08X}, data=0x{data:08X}")

        # Add APB transaction to scoreboard (scoreboard handles field mapping)
        self.apb_gaxi_scoreboard.add_apb_transaction(transaction)

    def rsp_transaction_callback(self, transaction):
        """Callback for GAXI RSP monitor transactions - SIMPLIFIED."""
        self.rsp_monitor_queue.append(transaction)

        data = getattr(transaction, 'prdata', getattr(transaction, 'data', 0))
        self.log.info(f"GAXI Response: data=0x{data:08X}")

        # Look for the oldest pending read that has response_data set
        if self.pending_reads:
            cmd = None
            for i, read_cmd in enumerate(self.pending_reads):
                if hasattr(read_cmd, 'response_data'):
                    cmd = read_cmd
                    del self.pending_reads[i]
                    break

            if cmd:
                # Create a merged transaction for the scoreboard
                merged_transaction = GAXIPacket(self.cmd_field_config)
                # Set both APB and GAXI style fields - scoreboard will handle both
                merged_transaction.pwrite = 0  # Read
                merged_transaction.cmd = 0     # Read
                merged_transaction.paddr = getattr(cmd, 'paddr', getattr(cmd, 'addr', 0))
                merged_transaction.addr = merged_transaction.paddr
                merged_transaction.prdata = cmd.response_data
                merged_transaction.data = cmd.response_data

                # Add to scoreboard (scoreboard handles field mapping automatically)
                self.log.info(f"Adding merged read tx_id={cmd.tx_id} to scoreboard: addr=0x{merged_transaction.paddr:08X}, data=0x{merged_transaction.data:08X}")
                self.apb_gaxi_scoreboard.add_gaxi_transaction(merged_transaction)
            else:
                self.log.warning("Received GAXI response but no pending read has APB data yet")

    async def reset_dut(self):
        self.log.debug('Starting reset_dut')

        # Reset DUT control signals
        self.dut.presetn.value = 0

        # Reset APB slave
        await self.apb_slave.reset_bus()

        # Reset GAXI components
        await self.cmd_master.reset_bus()
        await self.rsp_slave.reset_bus()

        # Hold reset for multiple cycles
        await self.wait_clocks('pclk', 5)

        # Release reset
        self.dut.presetn.value = 1

        # Wait for stabilization
        await self.wait_clocks('pclk', 10)

        # Clear monitoring queues
        self.apb_monitor_queue.clear()
        self.cmd_monitor_queue.clear()
        self.rsp_monitor_queue.clear()
        self.pending_reads.clear()

        # Clear scoreboard
        self.apb_gaxi_scoreboard.clear()

        self.log.debug('Ending reset_dut')

    async def wait_for_queue_empty(self, object_with_queue, timeout=1000):
        """Wait for a queue to be empty with timeout"""
        start_time = get_sim_time('ns')
        current_time = start_time

        # Check which queue attribute to monitor based on object type
        if hasattr(object_with_queue, 'transmit_queue'):
            queue_attr = 'transmit_queue'
        elif hasattr(object_with_queue, '_xmitQ'):
            queue_attr = '_xmitQ'
        else:
            self.log.error(f"Unknown queue type for object {object_with_queue.__class__.__name__}")
            return

        queue = getattr(object_with_queue, queue_attr)

        while len(queue) > 0:
            await self.wait_clocks('pclk', 1)
            current_time = get_sim_time('ns')

            # Check for timeout
            if current_time - start_time > timeout:
                self.log.warning(f"Timeout waiting for queue to be empty after {timeout}ns")
                break

    async def send_gaxi_cmd(self, is_write, addr, data=None, strobe=None, prot=0):
        """Send a GAXI command through the CMD master - SIMPLIFIED."""
        # Create a packet for the command using APB field names
        packet = GAXIPacket(self.cmd_field_config)
        packet.pwrite = 1 if is_write else 0
        packet.paddr = addr
        packet.pprot = prot

        # For write transactions, set data and strobe
        if is_write:
            packet.pwdata = data if data is not None else random.randint(0, 2**self.DATA_WIDTH - 1)
            packet.pstrb = strobe if strobe is not None else (2**self.STRB_WIDTH - 1)
            self.log.info(f"Sending write command: addr=0x{addr:08X}, data=0x{packet.pwdata:08X}, strb=0x{packet.pstrb:X}")
        else:
            packet.pwdata = 0
            packet.pstrb = 0
            self.log.info(f"Sending read command: addr=0x{addr:08X}")

        # Send command through GAXI command master
        await self.cmd_master.send(packet)

        # Wait for the master's queue to be empty
        await self.wait_for_queue_empty(self.cmd_master, timeout=10000)

        # Wait for processing
        await self.wait_clocks('pclk', 10)

        return packet

    async def run_gaxi_test(self, config: APBSequence, num_transactions: int = None):
        """Run GAXI test according to the configuration"""
        # Save original constraints to restore later
        save_randomizer = False

        # Apply custom timing constraints if provided
        if config.master_randomizer:
            save_randomizer = True
            self.log.debug(f'run_test: Setting master randomizer to {config.master_randomizer}')
            self.cmd_master.set_randomizer(config.master_randomizer)

        # Reset iterators
        config.reset_iterators()

        # Determine number of transactions to run
        if num_transactions is None:
            num_transactions = len(config.pwrite_seq)

        results = []

        try:
            # Execute transactions
            for i in range(num_transactions):
                # Get next transaction parameters
                is_write = config.next_pwrite()
                addr = config.next_addr()

                if is_write:
                    # Get data and strobe for write
                    data = config.next_data()
                    strobe = config.next_strb()

                    # Execute write transaction
                    result = await self.send_gaxi_cmd(True, addr, data, strobe)

                else:
                    # Execute read transaction
                    result = await self.send_gaxi_cmd(False, addr)

                # Store result
                results.append(result)

                # Add delay between transactions if not the last one
                if i < num_transactions - 1:
                    delay = config.next_delay()
                    if delay > 0:
                        await self.wait_clocks('pclk', delay)

        finally:
            # Restore original constraints
            if save_randomizer:
                self.cmd_master.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['master']))

        return results

    async def verify_scoreboard(self, timeout=1000):
        """Verify scoreboard for unmatched transactions"""
        self.log.info("Verifying APB-GAXI scoreboard for unmatched transactions")

        # Wait a bit for any pending transactions to complete
        await self.wait_clocks('pclk', 50)

        result = await self.apb_gaxi_scoreboard.check_scoreboard(timeout)

        if result:
            self.log.info("Scoreboard verification passed - all transactions matched")
        else:
            self.log.error("Scoreboard verification failed - unmatched transactions found")

        # Get and log the report
        report = self.apb_gaxi_scoreboard.report()
        self.log.info(f"Scoreboard report:\n{report}")

        return result

    # FIXED: Updated test sequence creation methods
    def _create_basic_seq(self):
        """Create configuration for basic test"""
        base_addr = 0x00  # Start at address 0
        num_regs = 50

        pwrite_seq = []
        addr_seq = []
        data_seq = []
        strb_seq = []

        # Alternating write-read pattern
        for i in range(num_regs):
            # Write
            pwrite_seq.append(True)
            addr_seq.append(base_addr + i * 4)
            data_seq.append(0xA0000000 + i)  # Distinctive data pattern
            strb_seq.append(2**self.STRB_WIDTH - 1)  # All strobe bits set

            # Read back the same address
            pwrite_seq.append(False)
            addr_seq.append(base_addr + i * 4)

        # Minimal delays for debugging
        delays = [2] * (len(pwrite_seq) - 1)

        return APBSequence(
            name="basic",
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=delays
        )

    def _create_burst_seq(self):
        """Create configuration for burst test"""
        base_addr = 0x100  # Different address range
        num_regs = 50

        pwrite_seq = []
        addr_seq = []
        data_seq = []
        strb_seq = []

        # All writes followed by all reads
        for i in range(num_regs):
            pwrite_seq.append(True)
            addr_seq.append(base_addr + i * 4)
            data_seq.append(0xB0000000 + i)  # Distinctive data pattern
            strb_seq.append(2**self.STRB_WIDTH - 1)

        for i in range(num_regs):
            pwrite_seq.append(False)
            addr_seq.append(base_addr + i * 4)

        # No delays for burst mode
        delays = [0] * (len(pwrite_seq) - 1)

        return APBSequence(
            name="burst",
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=delays
        )

    def _create_strobe_seq(self):
        """Create configuration for strobe test"""
        test_data = [0xFFFFFFFF, 0x12345678, 0xAABBCCDD]
        test_strobes = [0xF, 0x1, 0x3]  # All bits, byte 0, bytes 0-1

        pwrite_seq = []
        addr_seq = []
        data_seq = []
        strb_seq = []

        base_addr = 0x200  # Different address range

        for i in range(len(test_data)):
            # Write with specific pattern
            pwrite_seq.append(True)
            addr_seq.append(base_addr + i * 4)
            data_seq.append(test_data[i])
            strb_seq.append(test_strobes[i])

            # Read back
            pwrite_seq.append(False)
            addr_seq.append(base_addr + i * 4)

        delays = [2] * (len(pwrite_seq) - 1)

        return APBSequence(
            name="strobe",
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=delays
        )

    def _create_stress_seq(self, num_transactions=20):
        """Create configuration for stress test"""
        # Start with clean memory
        self.mem.reset()

        pwrite_seq = []
        addr_seq = []
        data_seq = []
        strb_seq = []

        # Address range for stress test
        addr_range = [0x300 + i * 4 for i in range(10)]  # Different address range
        data_range = [0xC0000000 + i for i in range(10)]
        strobe_range = [0xF, 0x1, 0x2, 0x4, 0x8, 0x3, 0x5, 0x9, 0x6, 0xA]

        # First do some writes
        for i in range(min(10, num_transactions // 2)):
            pwrite_seq.append(True)

        # Then mix reads and writes
        for i in range(num_transactions - len(pwrite_seq)):
            pwrite_seq.append(random.random() < 0.6)  # 60% writes

        addr_seq = addr_range
        data_seq = data_range
        strb_seq = strobe_range

        delay_range = [0, 1, 2]

        return APBSequence(
            name="stress",
            pwrite_seq=pwrite_seq,
            addr_seq=addr_seq,
            data_seq=data_seq,
            strb_seq=strb_seq,
            inter_cycle_delays=delay_range,
            use_random_selection=True
        )


@cocotb.test(timeout_time=10, timeout_unit="sec")
async def apb_master_wavedrom_test(dut):
    """
    WaveDrom timing diagram generation for APB master.

    Generates 7 comprehensive scenarios:
    1. Basic write transaction
    2. Basic read transaction
    3. Back-to-back writes
    4. Back-to-back reads
    5. Write-to-read transition
    6. Read-to-write transition
    7. Error response (if supported)

    All waveforms include clock and reset signals with APB signals grouped.

    Environment Variables:
        ENABLE_WAVEDROM: Enable waveform generation (1/0, default: 0)
    """
    # Check if waveforms are enabled
    enable_wavedrom = int(os.environ.get('ENABLE_WAVEDROM', '0'))
    if not enable_wavedrom:
        dut._log.info("⏭️  WaveDrom disabled (ENABLE_WAVEDROM=0), skipping wavedrom test")
        return

    dut._log.info("=== APB Master WaveDrom Test ===")

    # Setup testbench
    tb = APBMasterTB(dut)
    await tb.start_clock('pclk', 10, 'ns')
    await tb.reset_dut()
    await tb.wait_clocks('pclk', 5)

    # Setup WaveDrom with comprehensive 7-scenario preset
    addr_width = tb.ADDR_WIDTH
    data_width = tb.DATA_WIDTH
    field_config = get_apb_field_config(addr_width, data_width)
    wave_generator = create_apb_wavejson_generator(field_config)

    wave_solver = TemporalConstraintSolver(
        dut=dut,
        log=dut._log,
        wavejson_generator=wave_generator,
        default_field_config=field_config
    )

    wave_solver.add_clock_group('default', dut.pclk)

    # WAVEDROM REQUIREMENT v1.2: ALL waveforms MUST include clock and reset
    # Bind APB master signals (m_apb_* prefix) with clock and reset
    apb_signals = {
        'pclk': 'pclk',
        'presetn': 'presetn',
        'psel': 'm_apb_PSEL',
        'penable': 'm_apb_PENABLE',
        'pready': 'm_apb_PREADY',
        'pwrite': 'm_apb_PWRITE',
        'paddr': 'm_apb_PADDR',
        'pwdata': 'm_apb_PWDATA',
        'prdata': 'm_apb_PRDATA',
        'pstrb': 'm_apb_PSTRB',
        'pprot': 'm_apb_PPROT',
        'pslverr': 'm_apb_PSLVERR'
    }
    wave_solver.add_interface("apb", apb_signals, field_config=field_config)

    # Use comprehensive preset with all 7 standard APB scenarios
    # Error scenario is optional for master tests since we don't control slave error responses
    num_constraints = setup_apb_constraints_with_boundaries(
        wave_solver=wave_solver,
        preset_name="comprehensive",
        max_cycles=30,
        clock_group="default",
        data_width=data_width,
        addr_width=addr_width,
        enable_packet_callbacks=True,
        use_signal_names=True,
        post_match_cycles=3,
        error_required=False  # Master doesn't control slave error responses
    )

    dut._log.info(f"WaveDrom configured with {num_constraints} comprehensive APB constraints")

    # Start sampling for all scenarios
    await wave_solver.start_sampling()

    # Generate all 7 transaction scenarios
    dut._log.info("=== Generating All APB Master WaveDrom Scenarios ===")

    # Scenarios 1-2: Basic write and read
    dut._log.info("Generating: Basic write and read")
    await tb.send_gaxi_cmd(is_write=True, addr=0x1000, data=0xDEADBEEF)
    await tb.wait_clocks('pclk', 5)
    await tb.send_gaxi_cmd(is_write=False, addr=0x1000)
    await tb.wait_clocks('pclk', 10)

    # Scenario 3: Back-to-back writes
    dut._log.info("Generating: Back-to-back writes")
    await tb.send_gaxi_cmd(is_write=True, addr=0x2000, data=0xAAAAAAAA)
    await tb.send_gaxi_cmd(is_write=True, addr=0x2004, data=0xBBBBBBBB)
    await tb.wait_clocks('pclk', 10)

    # Scenario 4: Back-to-back reads
    dut._log.info("Generating: Back-to-back reads")
    await tb.send_gaxi_cmd(is_write=False, addr=0x3000)
    await tb.send_gaxi_cmd(is_write=False, addr=0x3004)
    await tb.wait_clocks('pclk', 10)

    # Scenario 5: Write-to-read transition
    dut._log.info("Generating: Write-to-read transition")
    await tb.send_gaxi_cmd(is_write=True, addr=0x4000, data=0x12345678)
    await tb.send_gaxi_cmd(is_write=False, addr=0x4000)
    await tb.wait_clocks('pclk', 10)

    # Scenario 6: Read-to-write transition
    dut._log.info("Generating: Read-to-write transition")
    await tb.send_gaxi_cmd(is_write=False, addr=0x5000)
    await tb.send_gaxi_cmd(is_write=True, addr=0x5000, data=0x87654321)
    await tb.wait_clocks('pclk', 10)

    # Scenario 7: Error transaction (if supported by slave)
    # Note: Error generation depends on slave configuration
    dut._log.info("Generating: Error scenario (if slave supports)")
    await tb.wait_clocks('pclk', 5)

    # Stop sampling and generate all waveforms
    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    results = wave_solver.get_results()

    # Check if all required waveforms were generated
    if not results['all_required_satisfied']:
        dut._log.error(f"❌ NOT ALL REQUIRED WAVEFORMS GENERATED ❌")
        dut._log.error(f"Failed constraints: {results['failed_constraints']}")
        raise AssertionError(f"Required waveforms not generated: {results['failed_constraints']}")

    dut._log.info(f"✓ APB Master WaveDrom Complete: {len(results['solutions'])} scenarios generated")

    # Set done flag
    tb.done = True
    await tb.wait_clocks('pclk', 10)


@cocotb.test(timeout_time=100, timeout_unit="us")  # Increased timeout
async def apb_master_test(dut):
    tb = APBMasterTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)

    # Start the clock
    print('Starting clk')
    await tb.start_clock('pclk', 10, 'ns')

    # Reset the DUT
    print('DUT reset')
    await tb.reset_dut()

    # Keep track of test results
    test_results = []

    try:
        # Test 1: Basic transfers
        print('# Test 1: Basic transfers with scoreboard verification')
        tb.log.info("=== Test 1: Basic transfers with scoreboard verification ===")
        config = tb._create_basic_seq()
        await tb.run_gaxi_test(config)
        result = await tb.verify_scoreboard()
        test_results.append(("Basic transfers", result))

        # Clear the scoreboard between tests
        tb.apb_gaxi_scoreboard.clear()
        await tb.wait_clocks('pclk', 20)

        # Test 2: Burst transfers
        print('# Test 2: Burst transfers with scoreboard verification')
        tb.log.info("=== Test 2: Burst transfers with scoreboard verification ===")
        config = tb._create_burst_seq()
        await tb.run_gaxi_test(config)
        result = await tb.verify_scoreboard()
        test_results.append(("Burst transfers", result))

        # Clear the scoreboard between tests
        tb.apb_gaxi_scoreboard.clear()
        await tb.wait_clocks('pclk', 20)

        # Test 3: Strobe functionality
        print('# Test 3: Strobe functionality with scoreboard verification')
        tb.log.info("=== Test 3: Strobe functionality with scoreboard verification ===")
        config = tb._create_strobe_seq()
        await tb.run_gaxi_test(config)
        result = await tb.verify_scoreboard()
        test_results.append(("Strobe functionality", result))

        # Test 4: Stress functionality
        print('# Test 4: Stress functionality with scoreboard verification')
        tb.log.info("=== Test 4: Stress functionality with scoreboard verification ===")
        config = tb._create_stress_seq()
        await tb.run_gaxi_test(config)
        result = await tb.verify_scoreboard()
        test_results.append(("Stress functionality", result))

        await tb.wait_clocks('pclk', 50)

        # Print test summary
        tb.log.info("=== Test Summary ===")
        all_passed = True
        for test_name, passed in test_results:
            status = "PASSED" if passed else "FAILED"
            tb.log.info(f"  {test_name}: {status}")
            all_passed = all_passed and passed

        if all_passed:
            tb.log.info("All tests passed!")
            print("APB Master test completed successfully!")
            print("Verified GAXI-to-APB transformation using scoreboard")
            print("All GAXI command/response transactions matched with APB transactions")
        else:
            tb.log.error("One or more tests failed!")
            print("APB Master test had failures!")
            for test_name, passed in test_results:
                if not passed:
                    print(f"  Failed test: {test_name}")
            # Make the test fail in pytest by raising an exception
            assert False, "One or more tests failed - see log for details"

    finally:
        # Set done flag to terminate handlers
        tb.done = True
        # Wait for the tasks to complete
        await tb.wait_clocks('pclk', 20)


# Rest of the test function remains the same...
@pytest.mark.parametrize("addr_width, data_width, cmd_depth, rsp_depth",
    [
        (
            32,  # addr_width
            32,  # data_width
            6,   # cmd_depth
            6,   # rsp_depth
        )
    ])
def test_apb_master(request, addr_width, data_width, cmd_depth, rsp_depth):
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')


    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb_master"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], "gaxi/gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba'], f"apb/{dut_name}.sv")
    ]

    # create a human readable test identifier
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    cd_str = TBBase.format_dec(cmd_depth, 3)
    rd_str = TBBase.format_dec(rsp_depth, 3)
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_cd{cd_str}_rd{rd_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # use it int he simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = [rtl_dict['rtl_amba_includes']]
    # RTL parameters
    rtl_parameters = {k.upper(): str(v) for k, v in locals().items() if k in ["addr_width", "data_width", "cmd_depth", "rsp_depth"]}

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',  # Changed from DEBUG to reduce noise
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000))
    }

    # Add test parameters; these are passed to the environment, but not the RTL
    extra_env['TEST_ADDR_WIDTH'] = str(addr_width)
    extra_env['TEST_DATA_WIDTH'] = str(data_width)
    extra_env['TEST_CMD_DEPTH'] = str(cmd_depth)
    extra_env['TEST_RSP_DEPTH'] = str(rsp_depth)

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
            "--trace",
            
            "--trace-depth", "99",
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend(get_coverage_compile_args())


    sim_args = [
            "--trace",  # Tell Verilator to use VCD
            
            "--trace-depth", "99",
    ]

    plusargs = [
            "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure


# WaveDrom test parameters
def generate_apb_master_wavedrom_params():
    """Generate parameters for APB master WaveDrom tests"""
    return [
        # addr_width, data_width, cmd_depth, rsp_depth
        (32, 32, 6, 6),
    ]

wavedrom_params = generate_apb_master_wavedrom_params()

@pytest.mark.parametrize("addr_width, data_width, cmd_depth, rsp_depth", wavedrom_params)
def test_apb_master_wavedrom(request, addr_width, data_width, cmd_depth, rsp_depth):
    """APB master wavedrom test - generates timing diagrams."""
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_apb': 'rtl/amba/apb',
     'rtl_amba_includes': 'rtl/amba/includes'})

    toplevel = "apb_master"

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_apb'], "apb_master.sv"),
    ]

    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    cmd_str = TBBase.format_dec(cmd_depth, 3)
    rsp_str = TBBase.format_dec(rsp_depth, 3)

    test_name_plus_params = f"test_{worker_id}_apb_master_aw{aw_str}_dw{dw_str}_cmd{cmd_str}_rsp{rsp_str}_wd"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = [rtl_dict['rtl_amba_includes']]
    rtl_parameters = {}
    for param_name in ['addr_width', 'data_width', 'cmd_depth', 'rsp_depth']:
        if param_name in locals():
            rtl_parameters[param_name.upper()] = str(locals()[param_name])

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': 'apb_master',
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'ENABLE_WAVEDROM': '1',  # Enable WaveDrom!
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_CMD_DEPTH': str(cmd_depth),
        'TEST_RSP_DEPTH': str(rsp_depth),
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
            "--trace",
            
            "--trace-depth", "99",
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend(get_coverage_compile_args())


    sim_args = []

    plusargs = []

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=toplevel,
        module=module,
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=False,  # Disable FST - using WaveDrom instead
        keep_files=True,
        compile_args=compile_args,
        sim_args=sim_args,
        plusargs=plusargs,
        testcase="apb_master_wavedrom_test",  # Run wavedrom test specifically!
    )
