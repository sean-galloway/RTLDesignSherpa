# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI4Scoreboard
# Purpose: AXI4 Scoreboard for Verification
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Scoreboard for Verification

This module provides scoreboard functionality for verifying AXI4 transactions.
"""

from collections import deque
from cocotb.utils import get_sim_time

from CocoTBFramework.scoreboards.base_scoreboard import BaseScoreboard
from CocoTBFramework.components.axi4.axi4_packet import AXI4Packet


class AXI4Scoreboard(BaseScoreboard):
    """
    Scoreboard for AXI4 protocol transactions.

    This class provides:
    - Tracking and matching of master and slave-side transactions
    - Protocol compliance checking
    - Transaction statistics
    """

    def __init__(self, name, id_width=8, addr_width=32, data_width=32, user_width=1, log=None):
        """
        Initialize AXI4 Scoreboard.

        Args:
            name: Scoreboard name
            id_width: Width of ID fields (default: 8)
            addr_width: Width of address fields (default: 32)
            data_width: Width of data fields (default: 32)
            user_width: Width of user fields (default: 1)
            log: Logger instance
        """
        super().__init__(name, log)

        # Additional counters for AXI4-specific statistics
        self.write_count = 0
        self.read_count = 0
        self.protocol_error_count = 0

        # Transaction queues
        self.master_writes = {}  # Maps IDs to master-side write transactions
        self.slave_writes = {}   # Maps IDs to slave-side write transactions
        self.master_reads = {}   # Maps IDs to master-side read transactions
        self.slave_reads = {}    # Maps IDs to slave-side read transactions

        # Store monitors for easy access
        self.master_monitor = None
        self.slave_monitor = None

        # Field dimensions
        self.id_width = id_width
        self.addr_width = addr_width
        self.data_width = data_width
        self.user_width = user_width

    def add_master_monitor(self, monitor):
        """Connect a master-side AXI4 monitor to the scoreboard"""
        self.master_monitor = monitor

        # Register callbacks
        monitor.set_write_callback(self._handle_master_write)
        monitor.set_read_callback(self._handle_master_read)

    def add_slave_monitor(self, monitor):
        """Connect a slave-side AXI4 monitor to the scoreboard"""
        self.slave_monitor = monitor

        # Register callbacks
        monitor.set_write_callback(self._handle_slave_write)
        monitor.set_read_callback(self._handle_slave_read)

    def _handle_master_write(self, id_value, transaction):
        """Process a completed write transaction from the master side"""
        self.master_writes[id_value] = transaction

        # Check for matching slave-side transaction
        if id_value in self.slave_writes and not self.slave_writes[id_value].get('matched', False):
            # Both sides have transactions, check if they match
            self._check_write_match(id_value, self.master_writes[id_value], self.slave_writes[id_value])

    def _handle_slave_write(self, id_value, transaction):
        """Process a completed write transaction from the slave side"""
        self.slave_writes[id_value] = transaction

        # Check for matching master-side transaction
        if id_value in self.master_writes and not self.master_writes[id_value].get('matched', False):
            # Both sides have transactions, check if they match
            self._check_write_match(id_value, self.master_writes[id_value], self.slave_writes[id_value])

    def _handle_master_read(self, id_value, transaction):
        """Process a completed read transaction from the master side"""
        self.master_reads[id_value] = transaction

        # Check for matching slave-side transaction
        if id_value in self.slave_reads and not self.slave_reads[id_value].get('matched', False):
            # Both sides have transactions, check if they match
            self._check_read_match(id_value, self.master_reads[id_value], self.slave_reads[id_value])

    def _handle_slave_read(self, id_value, transaction):
        """Process a completed read transaction from the slave side"""
        self.slave_reads[id_value] = transaction

        # Check for matching master-side transaction
        if id_value in self.master_reads and not self.master_reads[id_value].get('matched', False):
            # Both sides have transactions, check if they match
            self._check_read_match(id_value, self.master_reads[id_value], self.slave_reads[id_value])

    def _check_write_match(self, id_value, master_tx, slave_tx):
        """Check if master and slave-side write transactions match"""
        mismatches = []

        # Check AW fields
        if master_tx.get('aw_transaction') and slave_tx.get('aw_transaction'):
            master_aw = master_tx['aw_transaction']
            slave_aw = slave_tx['aw_transaction']

            # Check key fields
            if hasattr(master_aw, 'awaddr') and hasattr(slave_aw, 'awaddr') and master_aw.awaddr != slave_aw.awaddr:
                mismatches.append(f"AWADDR: master=0x{master_aw.awaddr:X}, slave=0x{slave_aw.awaddr:X}")

            if hasattr(master_aw, 'awlen') and hasattr(slave_aw, 'awlen') and master_aw.awlen != slave_aw.awlen:
                mismatches.append(f"AWLEN: master={master_aw.awlen}, slave={slave_aw.awlen}")

            if hasattr(master_aw, 'awsize') and hasattr(slave_aw, 'awsize') and master_aw.awsize != slave_aw.awsize:
                mismatches.append(f"AWSIZE: master={master_aw.awsize}, slave={slave_aw.awsize}")

            if hasattr(master_aw, 'awburst') and hasattr(slave_aw, 'awburst') and master_aw.awburst != slave_aw.awburst:
                mismatches.append(f"AWBURST: master={master_aw.awburst}, slave={slave_aw.awburst}")
        else:
            mismatches.append("Missing AW transaction on one side")

        # Check W data
        master_data = [w.wdata for w in master_tx.get('w_transactions', []) if hasattr(w, 'wdata')]
        slave_data = [w.wdata for w in slave_tx.get('w_transactions', []) if hasattr(w, 'wdata')]

        if len(master_data) != len(slave_data):
            mismatches.append(f"Data beat count: master={len(master_data)}, slave={len(slave_data)}")
        else:
            for i, (master_beat, slave_beat) in enumerate(zip(master_data, slave_data)):
                if master_beat != slave_beat:
                    mismatches.append(f"Data beat {i}: master=0x{master_beat:X}, slave=0x{slave_beat:X}")

        # Check B response
        if master_tx.get('b_transaction') and slave_tx.get('b_transaction'):
            master_b = master_tx['b_transaction']
            slave_b = slave_tx['b_transaction']

            if hasattr(master_b, 'bresp') and hasattr(slave_b, 'bresp') and master_b.bresp != slave_b.bresp:
                mismatches.append(f"BRESP: master={master_b.bresp}, slave={slave_b.bresp}")
        else:
            mismatches.append("Missing B transaction on one side")

        # Record result
        if mismatches:
            self.error_count += 1
            if self.log:
                self.log.error(f"Write transaction ID={id_value} has mismatches:")
                for mismatch in mismatches:
                    self.log.error(f"  {mismatch}")
        else:
            # Mark as matched
            master_tx['matched'] = True
            slave_tx['matched'] = True
            self.write_count += 1
            if self.log:
                self.log.debug(f"Write transaction ID={id_value} matched between master and slave")

    def _check_read_match(self, id_value, master_tx, slave_tx):
        """Check if master and slave-side read transactions match"""
        mismatches = []

        # Check AR fields
        if master_tx.get('ar_transaction') and slave_tx.get('ar_transaction'):
            master_ar = master_tx['ar_transaction']
            slave_ar = slave_tx['ar_transaction']

            # Check key fields
            if hasattr(master_ar, 'araddr') and hasattr(slave_ar, 'araddr') and master_ar.araddr != slave_ar.araddr:
                mismatches.append(f"ARADDR: master=0x{master_ar.araddr:X}, slave=0x{slave_ar.araddr:X}")

            if hasattr(master_ar, 'arlen') and hasattr(slave_ar, 'arlen') and master_ar.arlen != slave_ar.arlen:
                mismatches.append(f"ARLEN: master={master_ar.arlen}, slave={slave_ar.arlen}")

            if hasattr(master_ar, 'arsize') and hasattr(slave_ar, 'arsize') and master_ar.arsize != slave_ar.arsize:
                mismatches.append(f"ARSIZE: master={master_ar.arsize}, slave={slave_ar.arsize}")

            if hasattr(master_ar, 'arburst') and hasattr(slave_ar, 'arburst') and master_ar.arburst != slave_ar.arburst:
                mismatches.append(f"ARBURST: master={master_ar.arburst}, slave={slave_ar.arburst}")
        else:
            mismatches.append("Missing AR transaction on one side")

        # Check R data
        master_data = [r.rdata for r in master_tx.get('r_transactions', []) if hasattr(r, 'rdata')]
        slave_data = [r.rdata for r in slave_tx.get('r_transactions', []) if hasattr(r, 'rdata')]

        if len(master_data) != len(slave_data):
            mismatches.append(f"Data beat count: master={len(master_data)}, slave={len(slave_data)}")
        else:
            for i, (master_beat, slave_beat) in enumerate(zip(master_data, slave_data)):
                if master_beat != slave_beat:
                    mismatches.append(f"Data beat {i}: master=0x{master_beat:X}, slave=0x{slave_beat:X}")

        # Record result
        if mismatches:
            self.error_count += 1
            if self.log:
                self.log.error(f"Read transaction ID={id_value} has mismatches:")
                for mismatch in mismatches:
                    self.log.error(f"  {mismatch}")
        else:
            # Mark as matched
            master_tx['matched'] = True
            slave_tx['matched'] = True
            self.read_count += 1
            if self.log:
                self.log.debug(f"Read transaction ID={id_value} matched between master and slave")

    def report(self):
        """Generate comprehensive report of AXI4 transaction verification"""
        # Calculate unmatched transactions
        unmatched_writes = (
            len([tx for tx in self.master_writes.values() if not tx.get('matched', False)]) +
            len([tx for tx in self.slave_writes.values() if not tx.get('matched', False)])
        )

        unmatched_reads = (
            len([tx for tx in self.master_reads.values() if not tx.get('matched', False)]) +
            len([tx for tx in self.slave_reads.values() if not tx.get('matched', False)])
        )

        # Generate report
        report_lines = [
            f"{self.name} AXI4 Scoreboard Report",
            "-" * 50,
            f"Write transactions matched: {self.write_count}",
            f"Read transactions matched: {self.read_count}",
            f"Protocol errors: {self.protocol_error_count}",
            f"Data mismatches: {self.error_count}",
            f"Unmatched write transactions: {unmatched_writes}",
            f"Unmatched read transactions: {unmatched_reads}",
            "-" * 50,
            f"Total errors: {self.error_count + self.protocol_error_count + unmatched_writes + unmatched_reads}"
        ]

        report = "\n".join(report_lines)
        if self.log:
            self.log.info(report)

        return report

    def check_all_transactions_matched(self):
        """Check if all transactions have been matched"""
        # Check for unmatched writes
        unmatched_writes = (
            len([tx for tx in self.master_writes.values() if not tx.get('matched', False)]) +
            len([tx for tx in self.slave_writes.values() if not tx.get('matched', False)])
        )

        # Check for unmatched reads
        unmatched_reads = (
            len([tx for tx in self.master_reads.values() if not tx.get('matched', False)]) +
            len([tx for tx in self.slave_reads.values() if not tx.get('matched', False)])
        )

        # Return True if all matched
        return unmatched_writes == 0 and unmatched_reads == 0

    def clear(self):
        """Clear all transaction tracking and reset counters"""
        # Clear transaction tracking
        self.master_writes.clear()
        self.slave_writes.clear()
        self.master_reads.clear()
        self.slave_reads.clear()

        # Reset counters
        self.write_count = 0
        self.read_count = 0
        self.error_count = 0
        self.protocol_error_count = 0

        # Call parent clear
        super().clear()


class AXI4MemoryScoreboard(AXI4Scoreboard):
    """
    AXI4 scoreboard that uses a memory model for verification.

    This class extends the standard AXI4Scoreboard by:
    - Using a shared memory model as the "golden" reference
    - Verifying all memory operations against the model
    - Tracking out-of-order operations
    """

    def __init__(self, name, memory_model, id_width=8, addr_width=32, data_width=32, user_width=1, log=None):
        """
        Initialize AXI4 Memory Scoreboard.

        Args:
            name: Scoreboard name
            memory_model: Memory model to use as reference
            id_width: Width of ID fields (default: 8)
            addr_width: Width of address fields (default: 32)
            data_width: Width of data fields (default: 32)
            user_width: Width of user fields (default: 1)
            log: Logger instance
        """
        super().__init__(name, id_width, addr_width, data_width, user_width, log)

        # Store memory model
        self.memory_model = memory_model

        # Additional tracking for memory operations
        self.memory_writes = {}  # Write operations to memory
        self.memory_reads = {}   # Read operations from memory

    def add_write(self, addr, data, strb=None):
        """
        Add a memory write operation.

        Args:
            addr: Address to write to
            data: Data written
            strb: Write strobe mask (default: all enabled)
        """
        # Create a unique key for this operation
        op_id = len(self.memory_writes)
        timestamp = get_sim_time('ns')

        # Store operation
        self.memory_writes[op_id] = {
            'addr': addr,
            'data': data,
            'strb': strb if strb is not None else ((1 << (self.data_width // 8)) - 1),
            'time': timestamp,
            'verified': False
        }

        # Write to memory model if available
        if self.memory_model:
            try:
                # Convert data to bytearray
                data_bytes = self.memory_model.integer_to_bytearray(data, self.memory_model.bytes_per_line)

                # Write to memory
                self.memory_model.write(addr, data_bytes, strb)

                if self.log:
                    self.log.debug(f"Memory write: addr=0x{addr:X}, data=0x{data:X}, strb=0x{strb:X if strb else 'FF'}")
            except Exception as e:
                if self.log:
                    self.log.error(f"Error writing to memory: {e}")

    def verify_read(self, addr, data):
        """
        Verify a memory read operation.

        Args:
            addr: Address read from
            data: Data returned

        Returns:
            bool: True if read data matches expected data
        """
        # Check against memory model
        if self.memory_model:
            try:
                # Read from memory
                expected_bytes = self.memory_model.read(addr, self.memory_model.bytes_per_line)
                expected = self.memory_model.bytearray_to_integer(expected_bytes)

                # Compare with actual data
                if expected != data:
                    if self.log:
                        self.log.error(f"Memory read mismatch: addr=0x{addr:X}, expected=0x{expected:X}, actual=0x{data:X}")
                    self.error_count += 1
                    return False
                else:
                    if self.log:
                        self.log.debug(f"Memory read verified: addr=0x{addr:X}, data=0x{data:X}")
                    return True
            except Exception as e:
                if self.log:
                    self.log.error(f"Error reading from memory: {e}")
                self.error_count += 1
                return False

        # No memory model to verify against
        return True

    def report(self):
        """Generate comprehensive report including memory operations"""
        # Get standard report
        std_report = super().report()

        # Add memory-specific information
        mem_report = [
            "",
            "Memory Operations",
            "-" * 50,
            f"Memory writes: {len(self.memory_writes)}",
            f"Memory reads: {len(self.memory_reads)}",
        ]

        # Return combined report
        return std_report + "\n" + "\n".join(mem_report)
