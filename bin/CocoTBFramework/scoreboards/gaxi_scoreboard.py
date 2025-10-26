# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GAXIScoreboard
# Purpose: GAXI Scoreboard for verifying GAXI transactions - Updated for new field config a
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""GAXI Scoreboard for verifying GAXI transactions - Updated for new field config and packet classes"""
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from .base_scoreboard import BaseScoreboard


class GAXIScoreboard(BaseScoreboard):
    """Scoreboard for GAXI transactions"""

    def __init__(self, name, field_config, log=None):
        """
        Initialize the scoreboard with the given field configuration.

        Args:
            name: Name of the scoreboard
            field_config: Field configuration (FieldConfig object or dictionary)
            log: Logger instance
        """
        super().__init__(name, log)

        # Convert dict to FieldConfig if needed
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        else:
            self.field_config = field_config

    def _compare_transactions(self, expected, actual):
        """
        Compare GAXI packets for equality.

        Args:
            expected: Expected transaction
            actual: Actual transaction

        Returns:
            True if transactions match, False otherwise
        """
        if not isinstance(expected, GAXIPacket) or not isinstance(actual, GAXIPacket):
            if self.log:
                self.log.error(f"{self.name} - Invalid transaction types")
                self.log.error(f"  Expected type: {type(expected)}")
                self.log.error(f"  Actual type: {type(actual)}")
            return False

        # Use the built-in comparison in GAXIPacket
        # The new Packet class implements __eq__ that skips 'start_time', 'end_time'
        return expected == actual

    def _log_mismatch(self, expected, actual):
        """
        Enhanced mismatch logging for GAXI packets.

        Args:
            expected: Expected transaction
            actual: Actual transaction
        """
        if self.log:
            self.log.error(f"{self.name} - GAXI Packet mismatch:")

            # Use formatted method if available (from new Packet class)
            if hasattr(expected, 'formatted') and hasattr(actual, 'formatted'):
                self.log.error(f"  Expected: {expected.formatted(compact=True)}")
                self.log.error(f"  Actual:   {actual.formatted(compact=True)}")
            else:
                # Fallback to string representation
                self.log.error(f"  Expected: {expected}")
                self.log.error(f"  Actual:   {actual}")

            # Detailed field comparison
            # Check if we're using the new Packet class with fields dict
            if hasattr(expected, 'fields') and hasattr(actual, 'fields'):
                # Use field names from FieldConfig
                field_names = self.field_config.field_names() if hasattr(self.field_config, 'field_names') else self.field_config.keys()

                for field_name in field_names:
                    if field_name in expected.fields and field_name in actual.fields and expected.fields[field_name] != actual.fields[field_name]:
                        exp_val = expected.fields[field_name]
                        act_val = actual.fields[field_name]
                        self.log.error(f"  Field '{field_name}' mismatch: expected=0x{exp_val:X}, actual=0x{act_val:X}")
            else:
                # Legacy approach - compare attributes directly
                for field_name in self.field_config:
                    if hasattr(expected, field_name) and hasattr(actual, field_name):
                        exp_val = getattr(expected, field_name)
                        act_val = getattr(actual, field_name)
                        if exp_val != act_val:
                            self.log.error(f"  Field '{field_name}' mismatch: expected=0x{exp_val:X}, actual=0x{act_val:X}")


class TransformScoreboard(BaseScoreboard):
    """Scoreboard that handles protocol transformations"""

    def __init__(self, name, transformer, target_scoreboard, log=None):
        """
        Initialize a transform scoreboard.

        Args:
            name: Name of the scoreboard
            transformer: Transformer to convert transactions
            target_scoreboard: Target scoreboard for verification
            log: Logger instance
        """
        super().__init__(name, log)
        self.transformer = transformer
        self.target_scoreboard = target_scoreboard

    def add_expected(self, transaction):
        """
        Transform source transaction and add resulting transactions to expected queue.

        Args:
            transaction: Transaction to transform and add
        """
        transformed = self.transformer.transform(transaction)
        for trans in transformed:
            self.target_scoreboard.add_expected(trans)

    def add_actual(self, transaction):
        """
        Add actual transaction with channel information.

        Args:
            transaction: Actual transaction to add
        """
        self.target_scoreboard.add_actual(transaction)

    def report(self):
        """
        Generate report using target scoreboard.

        Returns:
            Error count from target scoreboard
        """
        return self.target_scoreboard.report()

    def clear(self):
        """Clear target scoreboard"""
        self.target_scoreboard.clear()


class GAXItoMemoryAdapter:
    """
    Adapter for memory model integration with GAXI packets.
    Converts between GAXI packets and memory read/write operations.
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
            'strb': 'strb'
        }

    def write_to_memory(self, packet):
        """
        Write packet data to memory model.

        Args:
            packet: GAXI packet with write data

        Returns:
            True if successful, False otherwise
        """
        try:
            # Extract fields
            addr_field = self.field_map.get('addr', 'addr')
            data_field = self.field_map.get('data', 'data')
            strb_field = self.field_map.get('strb', 'strb')

            # Check if we're using the new Packet class
            if hasattr(packet, 'fields'):
                # Use the fields dictionary
                if addr_field not in packet.fields or data_field not in packet.fields:
                    if self.log:
                        self.log.error(f"Missing required fields for memory write: {addr_field}, {data_field}")
                    return False

                addr = packet.fields[addr_field]
                data = packet.fields[data_field]
                strb = packet.fields.get(strb_field, 0xFF)
            else:
                # Legacy approach - use attributes
                if not hasattr(packet, addr_field) or not hasattr(packet, data_field):
                    if self.log:
                        self.log.error(f"Missing required fields for memory write: {addr_field}, {data_field}")
                    return False

                addr = getattr(packet, addr_field)
                data = getattr(packet, data_field)
                strb = getattr(packet, strb_field) if hasattr(packet, strb_field) else 0xFF

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

    def read_from_memory(self, packet):
        """
        Read data from memory model based on packet address.

        Args:
            packet: GAXI packet with address to read from

        Returns:
            Data value read from memory, or None if error
        """
        try:
            # Extract address field
            addr_field = self.field_map.get('addr', 'addr')

            # Check if we're using the new Packet class
            if hasattr(packet, 'fields'):
                # Use the fields dictionary
                if addr_field not in packet.fields:
                    if self.log:
                        self.log.error(f"Missing required field for memory read: {addr_field}")
                    return None

                addr = packet.fields[addr_field]
            else:
                # Legacy approach - use attributes
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
