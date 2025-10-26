# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PacketFactory
# Purpose: Generic Packet Factory - Works across all protocols (GAXI, FIFO, APB, etc.)
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""Generic Packet Factory - Works across all protocols (GAXI, FIFO, APB, etc.)"""
from typing import Type, Optional, Dict, Any, Union, List, Callable
from .packet import Packet
from .field_config import FieldConfig


class PacketFactory:
    """
    Generic factory for creating and managing packets across any protocol.
    Eliminates the need for packet_class parameters and provides better abstraction.
    """

    def __init__(self, packet_class: Type[Packet], field_config: FieldConfig):
        """
        Initialize packet factory.

        Args:
            packet_class: Class to use for packet creation
            field_config: Field configuration for packets
        """
        self.packet_class = packet_class
        self.field_config = field_config

        # Validate that packet_class is actually a Packet subclass
        if not issubclass(packet_class, Packet):
            raise TypeError(f"packet_class must be a subclass of Packet, got {packet_class}")

    def create_packet(self, **kwargs) -> Packet:
        """
        Create a new packet with the configured class and field config.

        Args:
            **kwargs: Initial field values

        Returns:
            New packet instance
        """
        return self.packet_class(self.field_config, **kwargs)

    def create_timed_packet(self, start_time: Optional[float] = None, **kwargs) -> Packet:
        """
        Create a packet with timing information.

        Args:
            start_time: Start time in simulation time units
            **kwargs: Initial field values

        Returns:
            New packet with start_time set
        """
        packet = self.create_packet(**kwargs)
        if start_time is not None:
            packet.start_time = start_time
        return packet

    def finish_packet(self, packet: Packet, end_time: Optional[float] = None,
                        data_dict: Optional[Dict[str, Any]] = None) -> Packet:
        """
        Complete a packet with data and timing information.

        Args:
            packet: Packet to complete
            end_time: End time in simulation time units
            data_dict: Field data to unpack into packet

        Returns:
            The completed packet (for chaining)
        """
        # Set end time
        if end_time is not None:
            packet.end_time = end_time

        # Unpack data if provided
        if data_dict:
            packet.unpack_from_fifo(data_dict)

        return packet

    def create_from_data(self, data_dict: Dict[str, Any],
                        start_time: Optional[float] = None,
                        end_time: Optional[float] = None) -> Packet:
        """
        Create a packet directly from field data.

        Args:
            data_dict: Field values
            start_time: Optional start time
            end_time: Optional end time

        Returns:
            New packet with data and timing
        """
        packet = self.create_timed_packet(start_time)
        return self.finish_packet(packet, end_time, data_dict)

    def create_random_packet(self, randomizer=None, **fixed_fields) -> Packet:
        """
        Create a packet with random field values.

        Args:
            randomizer: Optional randomizer to use for field values
            **fixed_fields: Fields with fixed values (override random)

        Returns:
            New packet with random/fixed field values
        """
        packet = self.create_packet(**fixed_fields)

        # If randomizer provided, use it to set random values for unset fields
        if randomizer and hasattr(randomizer, 'randomize_packet'):
            randomizer.randomize_packet(packet)

        return packet

    def copy_packet(self, source_packet: Packet, **overrides) -> Packet:
        """
        Create a copy of an existing packet with optional field overrides.

        Args:
            source_packet: Packet to copy
            **overrides: Fields to override in the copy

        Returns:
            New packet that's a copy of the source
        """
        copied = source_packet.copy()

        # Apply any overrides
        for field_name, value in overrides.items():
            setattr(copied, field_name, value)

        return copied

    def validate_packet(self, packet: Packet) -> bool:
        """
        Validate that a packet has all required fields set.

        Args:
            packet: Packet to validate

        Returns:
            True if packet is valid, False otherwise
        """
        for field_name in self.field_config.field_names():
            if not hasattr(packet, field_name):
                return False
            value = getattr(packet, field_name)
            if value is None or value == -1:  # -1 indicates X/Z value
                return False
        return True


class TransactionHandler:
    """
    Generic handler for transaction processing across any protocol.
    Encapsulates common transaction patterns used by masters, slaves, and monitors.
    """

    def __init__(self, packet_factory: PacketFactory, callbacks: List[Callable],
                    log, component_name: str):
        """
        Initialize transaction handler.

        Args:
            packet_factory: Factory for creating packets
            callbacks: List of callback functions
            log: Logger instance
            component_name: Name for logging
        """
        self.factory = packet_factory
        self.callbacks = callbacks
        self.log = log
        self.component_name = component_name

        # Statistics
        self.stats = {
            'transactions_processed': 0,
            'callback_errors': 0,
            'validation_failures': 0
        }

    def create_transaction(self, start_time: float, **initial_fields) -> Packet:
        """Create a new transaction packet with start time and initial fields."""
        self.stats['transactions_processed'] += 1
        return self.factory.create_timed_packet(start_time=start_time, **initial_fields)

    def finish_transaction(self, packet: Packet, end_time: float,
                            data_dict: Optional[Dict[str, Any]] = None,
                            validate: bool = True) -> Packet:
        """
        Complete a transaction and trigger callbacks.

        Args:
            packet: Packet to complete
            end_time: Transaction end time
            data_dict: Optional field data
            validate: Whether to validate packet before callbacks

        Returns:
            Completed packet
        """
        # Complete the packet
        completed_packet = self.factory.finish_packet(packet, end_time, data_dict)

        # Validate if requested
        if validate and not self.factory.validate_packet(completed_packet):
            self.log.warning(f"{self.component_name}: Packet validation failed")
            self.stats['validation_failures'] += 1

        # Log the transaction
        self._log_transaction(completed_packet)

        # Trigger callbacks
        self._trigger_callbacks(completed_packet)

        return completed_packet

    def _log_transaction(self, packet: Packet):
        """Log a completed transaction."""
        packet_str = (packet.formatted(compact=True)
                        if hasattr(packet, 'formatted')
                            else str(packet))
        self.log.debug(f"{self.component_name} Transaction at {packet.end_time}ns: {packet_str}")

    def _trigger_callbacks(self, packet: Packet):
        """Trigger all registered callbacks with error handling."""
        for callback in self.callbacks:
            try:
                callback(packet)
            except Exception as e:
                self.log.error(f"{self.component_name} Error in callback: {e}")
                self.stats['callback_errors'] += 1

    def add_callback(self, callback: Callable):
        """Add a new callback function."""
        if callback not in self.callbacks:
            self.callbacks.append(callback)

    def remove_callback(self, callback: Callable):
        """Remove a callback function."""
        if callback in self.callbacks:
            self.callbacks.remove(callback)

    def get_stats(self) -> Dict[str, Any]:
        """Get transaction processing statistics."""
        return self.stats.copy()


class FieldUnpacker:
    """
    Generic helper for unpacking combined field values into individual fields.
    Works across any protocol by using field configuration information.
    """

    def __init__(self, field_config: FieldConfig, log, component_name: str):
        """
        Initialize field unpacker.

        Args:
            field_config: Field configuration
            log: Logger instance
            component_name: Component name for logging
        """
        self.field_config = field_config
        self.log = log
        self.component_name = component_name

    def unpack_combined_fields(self, combined_value: int) -> Dict[str, int]:
        """
        Unpack a combined value into individual fields.

        Args:
            combined_value: Combined integer value containing all fields

        Returns:
            Dictionary of field_name -> field_value mappings
        """
        unpacked_fields = {}
        bit_offset = 0

        # Process fields in the order defined in field_config
        for field_name in self.field_config.field_names():
            # Get field definition
            field_def = self.field_config.get_field(field_name)
            field_width = field_def.bits
            mask = (1 << field_width) - 1

            # Extract field value using mask and shift
            field_value = (combined_value >> bit_offset) & mask

            # Check for field overflow
            field_value = self._check_field_value(field_name, field_value, field_width)

            unpacked_fields[field_name] = field_value
            bit_offset += field_width

        return unpacked_fields

    def _check_field_value(self, field_name: str, field_value: int, field_width: int) -> int:
        """Check if a field value exceeds the maximum for the field."""
        max_value = (1 << field_width) - 1

        if field_value > max_value:
            self.log.warning(
                f"{self.component_name}: Field '{field_name}' value 0x{field_value:X} "
                f"exceeds maximum 0x{max_value:X} ({field_width} bits). Value will be masked."
            )
            return field_value & max_value

        return field_value


def create_packet_system(packet_class: Type[Packet], field_config: FieldConfig,
                        log, component_name: str, callbacks: Optional[List[Callable]] = None):
    """
    Create a complete packet handling system for any protocol component.

    Args:
        packet_class: Packet class to use
        field_config: Field configuration
        log: Logger
        component_name: Component name for logging
        callbacks: Optional initial callback functions

    Returns:
        Tuple of (PacketFactory, TransactionHandler, FieldUnpacker)
    """
    callbacks = callbacks or []

    factory = PacketFactory(packet_class, field_config)
    handler = TransactionHandler(factory, callbacks, log, component_name)
    unpacker = FieldUnpacker(field_config, log, component_name)

    return factory, handler, unpacker


def create_monitor_system(packet_class: Type[Packet], field_config: FieldConfig,
                            log, component_name: str, callbacks: Optional[List[Callable]] = None):
    """
    Create a packet system optimized for monitors.

    Args:
        packet_class: Packet class to use
        field_config: Field configuration
        log: Logger
        component_name: Component name for logging
        callbacks: Optional callback functions for received packets

    Returns:
        Tuple of (PacketFactory, TransactionHandler, FieldUnpacker)
    """
    return create_packet_system(packet_class, field_config, log, component_name, callbacks)


def create_master_system(packet_class: Type[Packet], field_config: FieldConfig,
                        log, component_name: str):
    """
    Create a packet system optimized for masters.

    Args:
        packet_class: Packet class to use
        field_config: Field configuration
        log: Logger
        component_name: Component name for logging

    Returns:
        PacketFactory instance (masters typically don't need full TransactionHandler)
    """
    return PacketFactory(packet_class, field_config)


def create_slave_system(packet_class: Type[Packet], field_config: FieldConfig,
                        log, component_name: str, callbacks: Optional[List[Callable]] = None):
    """
    Create a packet system optimized for slaves.

    Args:
        packet_class: Packet class to use
        field_config: Field configuration
        log: Logger
        component_name: Component name for logging
        callbacks: Optional callback functions for processed packets

    Returns:
        Tuple of (PacketFactory, TransactionHandler, FieldUnpacker)
    """
    return create_packet_system(packet_class, field_config, log, component_name, callbacks)
