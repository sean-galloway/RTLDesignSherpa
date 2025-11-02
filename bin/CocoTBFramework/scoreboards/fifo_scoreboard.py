# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FIFOScoreboard
# Purpose: FIFO Scoreboard for verifying FIFO transactions
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""FIFO Scoreboard for verifying FIFO transactions"""
from CocoTBFramework.components.fifo.fifo_packet import FIFOPacket
from CocoTBFramework.scoreboards.base_scoreboard import BaseScoreboard


class FIFOScoreboard(BaseScoreboard):
    """Scoreboard for FIFO transactions"""

    def __init__(self, name, field_config, log=None):
        super().__init__(name, log)
        self.field_config = field_config

    def _compare_transactions(self, expected, actual):
        """Compare FIFO packets"""
        if not isinstance(expected, FIFOPacket) or not isinstance(actual, FIFOPacket):
            if self.log:
                self.log.error(f"{self.name} - Invalid transaction types")
                self.log.error(f"  Expected type: {type(expected)}")
                self.log.error(f"  Actual type: {type(actual)}")
            return False

        # Use the built-in comparison in FIFOPacket
        return expected == actual

    def _log_mismatch(self, expected, actual):
        """Enhanced mismatch logging for FIFO packets"""
        if self.log:
            self.log.error(f"{self.name} - FIFO Packet mismatch:")
            self.log.error(f"  Expected: {expected.formatted(compact=True)}")
            self.log.error(f"  Actual:   {actual.formatted(compact=True)}")

            # Detailed field comparison
            for field_name in self.field_config:
                if field_name in expected.fields and field_name in actual.fields and expected.fields[field_name] != actual.fields[field_name]:
                    exp_val = expected.fields[field_name]
                    act_val = actual.fields[field_name]
                    self.log.error(f"  Field '{field_name}' mismatch: expected=0x{exp_val:X}, actual=0x{act_val:X}")


class MemoryAdapter:
    """
    Adapter for memory model integration with FIFO packets.
    Converts between FIFO packets and memory read/write operations.
    """

    def __init__(self, memory_model, field_map=None, log=None):
        """
        Initialize the adapter.

        Args:
            memory_model: Memory model for storage
            field_map: Mapping of memory operations to packet fields
            log: Logger
        """
        self.memory_model = memory_model
        self.log = log

        # Default field mapping if not provided
        self.field_map = field_map or {
            'addr': 'addr',
            'data': 'data',
            'ctrl': 'ctrl'
        }

    def write_to_memory(self, packet):  # sourcery skip: extract-method
        """
        Write packet data to memory model.

        Args:
            packet: FIFO packet with write data

        Returns:
            True if successful, False otherwise
        """
        try:
            # Extract fields
            addr_field = self.field_map.get('addr', 'addr')
            data_field = self.field_map.get('data', 'data')
            ctrl_field = self.field_map.get('ctrl', 'ctrl')

            if not hasattr(packet, addr_field) or not hasattr(packet, data_field):
                if self.log:
                    self.log.error(f"Missing required fields for memory write: {addr_field}, {data_field}")
                return False

            addr = getattr(packet, addr_field)
            data = getattr(packet, data_field)
            # Ctrl field can be used as a mask (strobe) for memory writes
            strb = getattr(packet, ctrl_field) if hasattr(packet, ctrl_field) else 0xFF

            # Convert data to bytearray
            data_bytes = self.memory_model.integer_to_bytearray(data, self.memory_model.bytes_per_line)

            # Write to memory
            self.memory_model.write(addr, data_bytes, strb)
            if self.log:
                self.log.debug(f"Memory write: addr=0x{addr:X}, data=0x{data:X}, strb=0x{strb:X}")

            return True
        except Exception as e:
            if self.log:
                self.log.error(f"Error writing to memory: {e}")
            return False

    def read_from_memory(self, packet):  # sourcery skip: extract-method
        """
        Read data from memory model based on packet address.

        Args:
            packet: FIFO packet with address to read from

        Returns:
            Data value read from memory, or None if error
        """
        try:
            # Extract address field
            addr_field = self.field_map.get('addr', 'addr')

            if not hasattr(packet, addr_field):
                if self.log:
                    self.log.error(f"Missing required field for memory read: {addr_field}")
                return None

            addr = getattr(packet, addr_field)

            # Read from memory
            data_bytes = self.memory_model.read(addr, self.memory_model.bytes_per_line)
            data = self.memory_model.bytearray_to_integer(data_bytes)

            if self.log:
                self.log.debug(f"Memory read: addr=0x{addr:X}, data=0x{data:X}")

            return data
        except Exception as e:
            if self.log:
                self.log.error(f"Error reading from memory: {e}")
            return None
