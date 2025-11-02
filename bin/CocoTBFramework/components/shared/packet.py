# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: _FieldCache
# Purpose: Generic Packet Class for Protocol Testing with Thread-Safe Performance Optimizat
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Generic Packet Class for Protocol Testing with Thread-Safe Performance Optimizations

This module provides an optimized base Packet class that can be used across different protocols
(GAXI, APB, etc.) to handle common packet operations like field management, formatting,
and comparisons with enhanced performance through thread-safe caching.

UPDATED: Made field cache thread-safe for parallel test execution.
"""
import threading
from typing import Dict, Any, List, Optional, Union, Tuple
from .field_config import FieldConfig


# Thread-safe cache for field operations
class _FieldCache:
    """Thread-safe cache for field operations to improve performance in parallel testing"""

    def __init__(self):
        """Initialize empty caches with thread safety"""
        # Field masks cache: (field_config_id, field_name) -> mask
        self.field_masks = {}

        # Field bits cache: (field_config_id, field_name) -> bits
        self.field_bits = {}

        # Field active bits cache: (field_config_id, field_name) -> (msb, lsb)
        self.field_active_bits = {}

        # Field format cache: (field_config_id, field_name) -> format_function
        self.field_formatters = {}

        # Field encoding cache: (field_config_id, field_name) -> encoding_dict
        self.field_encodings = {}

        # Statistics
        self.hits = 0
        self.misses = 0

        # Thread safety
        self._lock = threading.RLock()

    def get_mask(self, field_config: FieldConfig, field_name: str) -> int:
        """Get mask for a field (thread-safe cached)"""
        # Create a cache key using the field_config's id and field name
        cache_key = (id(field_config), field_name)

        with self._lock:
            if cache_key in self.field_masks:
                self.hits += 1
                return self.field_masks[cache_key]

            # Cache miss, calculate mask
            self.misses += 1
            if not field_config.has_field(field_name):
                # Default to all bits if field not found
                mask = 0xFFFFFFFF
            else:
                field_def = field_config.get_field(field_name)
                bits = field_def.bits
                mask = (1 << bits) - 1

            # Store in cache
            self.field_masks[cache_key] = mask
            return mask

    def get_bits(self, field_config: FieldConfig, field_name: str) -> int:
        """Get bits for a field (thread-safe cached)"""
        cache_key = (id(field_config), field_name)

        with self._lock:
            if cache_key in self.field_bits:
                self.hits += 1
                return self.field_bits[cache_key]

            # Cache miss, calculate bits
            self.misses += 1
            if not field_config.has_field(field_name):
                # Default to 32 bits if field not found
                bits = 32
            else:
                field_def = field_config.get_field(field_name)
                bits = field_def.bits

            # Store in cache
            self.field_bits[cache_key] = bits
            return bits

    def get_active_bits(self, field_config: FieldConfig, field_name: str) -> Tuple[int, int]:
        """Get active bits (msb, lsb) for a field (thread-safe cached)"""
        cache_key = (id(field_config), field_name)

        with self._lock:
            if cache_key in self.field_active_bits:
                self.hits += 1
                return self.field_active_bits[cache_key]

            # Cache miss, calculate active bits
            self.misses += 1
            if not field_config.has_field(field_name):
                # Default to full width if field not found
                bits = 32
                active_bits = (bits - 1, 0)
            else:
                field_def = field_config.get_field(field_name)
                active_bits = field_def.active_bits

            # Store in cache
            self.field_active_bits[cache_key] = active_bits
            return active_bits

    def get_formatter(self, field_config: FieldConfig, field_name: str):
        """Get a formatting function for a field (thread-safe cached)"""
        cache_key = (id(field_config), field_name)

        with self._lock:
            if cache_key in self.field_formatters:
                self.hits += 1
                return self.field_formatters[cache_key]

            # Cache miss, create formatter
            self.misses += 1
            if not field_config.has_field(field_name):
                # Default to hex format if field not found
                formatter = lambda value: f"0x{value:X}"
            else:
                field_def = field_config.get_field(field_name)
                fmt = field_def.format
                width = field_def.display_width

                if fmt == 'bin':
                    formatter = lambda value: f"0b{value:0{width}b}"
                elif fmt == 'dec':
                    formatter = lambda value: f"{value:{width}d}"
                else:
                    # Default to hex
                    formatter = lambda value: f"0x{value:0{width}X}"

            # Store in cache
            self.field_formatters[cache_key] = formatter
            return formatter

    def get_encoding(self, field_config: FieldConfig, field_name: str) -> Optional[Dict[int, str]]:
        """Get encoding dictionary for a field (thread-safe cached)"""
        cache_key = (id(field_config), field_name)

        with self._lock:
            if cache_key in self.field_encodings:
                self.hits += 1
                return self.field_encodings[cache_key]

            # Cache miss, get encoding
            self.misses += 1
            if not field_config.has_field(field_name):
                # No encoding if field not found
                encoding = None
            else:
                field_def = field_config.get_field(field_name)
                encoding = field_def.encoding if hasattr(field_def, 'encoding') else None

            # Store in cache
            self.field_encodings[cache_key] = encoding
            return encoding

    def clear(self):
        """Clear all caches (thread-safe)"""
        with self._lock:
            self.field_masks.clear()
            self.field_bits.clear()
            self.field_active_bits.clear()
            self.field_formatters.clear()
            self.field_encodings.clear()
            self.hits = 0
            self.misses = 0

    def get_stats(self) -> Dict[str, Any]:
        """Get cache statistics (thread-safe)"""
        with self._lock:
            total = self.hits + self.misses
            hit_rate = (self.hits / total * 100) if total > 0 else 0

            return {
                'hits': self.hits,
                'misses': self.misses,
                'hit_rate': hit_rate,
                'cache_size': {
                    'masks': len(self.field_masks),
                    'bits': len(self.field_bits),
                    'active_bits': len(self.field_active_bits),
                    'formatters': len(self.field_formatters),
                    'encodings': len(self.field_encodings)
                },
                'thread_safe': True
            }


# Create global thread-safe cache instance
_FIELD_CACHE = _FieldCache()


def get_field_cache_stats() -> Dict[str, Any]:
    """Get field cache statistics (thread-safe)"""
    return _FIELD_CACHE.get_stats()


def clear_field_cache():
    """Clear the field cache (thread-safe)"""
    _FIELD_CACHE.clear()


class Packet:
    """
    Generic packet class for handling protocol transactions with thread-safe optimized performance.

    This class provides a flexible way to define packets with custom fields without
    requiring subclassing for each protocol. Fields are defined through a FieldConfig
    object, and the class handles bit field transformations automatically during
    packing/unpacking.

    Performance optimizations include:
    - Thread-safe caching of field masks, bits, and formatters
    - Fast field lookup and validation
    - Optimized bit shifting operations for pack/unpack
    - Safe parallel test execution
    """

    def __init__(self, field_config: Union[FieldConfig, Dict[str, Dict[str, Any]]],
                 skip_compare_fields: Optional[List[str]] = None, **kwargs):
        """
        Initialize a packet with the given field configuration.

        Args:
            field_config: Either a FieldConfig object or a dictionary of field definitions
            skip_compare_fields: List of field names to skip during comparison operations
            **kwargs: Initial values for fields (e.g., addr=0x123, data=0xABC)
        """
        # Initialize core attributes using object.__setattr__ to avoid recursion
        object.__setattr__(self, 'start_time', 0)
        object.__setattr__(self, 'end_time', 0)
        object.__setattr__(self, 'fields', {})

        # Convert dictionary field_config to FieldConfig object if needed
        if isinstance(field_config, dict):
            object.__setattr__(self, 'field_config', FieldConfig.validate_and_create(field_config))
        else:
            object.__setattr__(self, 'field_config', field_config)

        # Set fields to skip during comparison
        object.__setattr__(self, 'skip_compare_fields', skip_compare_fields or ['start_time', 'end_time'])

        # Initialize all fields with their default values
        for name, field_def in self.field_config.items():
            self.fields[name] = field_def.default

        # Set any provided initial values
        for field_name, value in kwargs.items():
            if field_name in self.fields:
                # Use __setattr__ to ensure masking is applied
                setattr(self, field_name, value)

    def mask_field_value(self, value, field_name):
        """
        Mask a value to ensure it doesn't exceed the bit width of the specified field.

        This is useful to prevent values from overflowing their assigned fields.
        The mask is created based on the field's bit width, not just the active bits.
        Uses thread-safe caching for better performance.

        Args:
            value: The value to mask
            field_name: Name of the field whose bit width determines the mask

        Returns:
            Value masked to fit within the field's bit width

        Raises:
            AttributeError: If the field doesn't exist
        """
        if not self.field_config.has_field(field_name):
            raise AttributeError(f"No field named '{field_name}' exists in this packet")

        # Get mask from thread-safe cache
        mask = _FIELD_CACHE.get_mask(self.field_config, field_name)

        # Apply mask to truncate any bits beyond the field width
        masked_value = value & mask

        # If the value was changed by masking, log a warning
        if masked_value != value:
            print(f"WARNING: Value 0x{value:X} exceeds bit width for field '{field_name}', masked to 0x{masked_value:X}")

        return masked_value

    def __getattr__(self, name):
        """
        Support direct attribute access for fields.

        Args:
            name: Field name to access

        Returns:
            Field value if it exists

        Raises:
            AttributeError: If the field doesn't exist
        """
        # This method is only called for attributes that don't exist in the instance's __dict__
        if 'fields' in self.__dict__ and name in self.__dict__['fields']:
            return self.__dict__['fields'][name]
        raise AttributeError(f"'{self.__class__.__name__}' object has no attribute '{name}'")

    def __setattr__(self, name, value):
        """
        Support direct attribute assignment for fields with automatic value masking.

        Args:
            name: Field name to set
            value: Value to assign (will be masked to fit field width)
        """
        # Check if we have fields initialized and if name is a field
        if 'fields' in self.__dict__ and name in self.__dict__['fields']:
            # Apply masking before setting the field value
            masked_value = self.mask_field_value(value, name)
            # Set field value in the fields dictionary
            self.__dict__['fields'][name] = masked_value
        else:
            # Set as regular attribute
            object.__setattr__(self, name, value)

    def shift_for_fifo(self, value, field_name):
        """
        Convert a full field value to its FIFO representation by right-shifting.
        For example, if addr[31:5] is 0x12345678, this returns 0x91A2B3 (shifted right by 5).

        Uses thread-safe caching for better performance.

        Args:
            value: The full field value
            field_name: Name of the field

        Returns:
            Value adjusted according to active_bits configuration for FIFO
        """
        if not self.field_config.has_field(field_name):
            return value

        # Get active bits from thread-safe cache
        active_bits = _FIELD_CACHE.get_active_bits(self.field_config, field_name)

        if active_bits[1] == 0:
            return value

        # Extract only the active bits by right-shifting
        msb, lsb = active_bits
        shifted_value = value >> lsb

        # Create a mask for the active bits
        active_width = msb - lsb + 1
        mask = (1 << active_width) - 1

        # Apply the mask to ensure we only keep the active bits
        return shifted_value & mask

    def expand_from_fifo(self, value, field_name):
        """
        Expand a FIFO value to its full field representation by left-shifting.
        For example, if addr[31:5] in FIFO is 0x91A2B3, this returns 0x12345660 (shifted left by 5).
        Note that the lowest 5 bits will be zeros due to the shifting process.

        Uses thread-safe caching for better performance.

        Args:
            value: The FIFO field value
            field_name: Name of the field

        Returns:
            Value expanded according to active_bits configuration
        """
        if not self.field_config.has_field(field_name):
            return value

        # Get active bits from thread-safe cache
        active_bits = _FIELD_CACHE.get_active_bits(self.field_config, field_name)

        return value if active_bits[1] == 0 else value << active_bits[1]

    def pack_for_fifo(self):
        """
        Pack the packet into a dictionary suitable for FIFO transmission,
        applying appropriate bit field adjustments.

        Returns:
            Dictionary with field name and FIFO-adjusted values
        """
        fifo_data = {}
        for field_name, value in self.fields.items():
            # Apply bit shifting for FIFO
            fifo_value = self.shift_for_fifo(value, field_name)
            fifo_data[field_name] = fifo_value
        return fifo_data

    def unpack_from_fifo(self, fifo_data):
        """
        Unpack FIFO data into full field values, applying appropriate bit field expansions.
        Values are automatically masked to fit within the defined field widths.

        Args:
            fifo_data: Dictionary with field values from FIFO, or a single integer value
                (which will be assigned to 'data' field if present)

        Returns:
            Self for chaining
        """
        # Handle both dictionary input and single value input
        if isinstance(fifo_data, dict):
            # Process dictionary of field values
            for field_name, fifo_value in fifo_data.items():
                if field_name in self.fields:
                    # Expand from FIFO value to full field value
                    full_value = self.expand_from_fifo(fifo_value, field_name)
                    # Apply masking to ensure the value fits the field
                    masked_value = self.mask_field_value(full_value, field_name)
                    self.fields[field_name] = masked_value
        elif isinstance(fifo_data, int) and 'data' in self.fields:
            # Handle case when a single integer value is provided
            full_value = self.expand_from_fifo(fifo_data, 'data')
            masked_value = self.mask_field_value(full_value, 'data')
            self.fields['data'] = masked_value

        return self

    def get_total_bits(self):
        """
        Calculate the total number of bits in the packet.

        Returns:
            Total number of bits across all fields
        """
        return self.field_config.get_total_bits()

    def _get_basic_format(self, field_name, value):
        """
        Get the basic formatted value without encoding.

        Args:
            field_name: Name of the field
            value: Value to format

        Returns:
            Basic formatted string representation of the value
        """
        formatter = _FIELD_CACHE.get_formatter(self.field_config, field_name)
        return formatter(value)

    def _format_field(self, field_name, value):
        """
        Format a field value according to its configuration.
        If an encoding is defined for the field, use the state name.

        Uses thread-safe caching for better performance.

        Args:
            field_name: Name of the field to format
            value: Value to format

        Returns:
            Formatted string representation of the value
        """
        if not self.field_config.has_field(field_name):
            return str(value)

        # Check for undefined values
        if value == -1:
            return "X/Z"  # Indicate undefined value

        # Check if field has encoding
        encoding = _FIELD_CACHE.get_encoding(self.field_config, field_name)

        if encoding and value in encoding:
            # Use the encoded state name with raw value in parentheses
            state_name = encoding[value]
            raw_format = self._get_basic_format(field_name, value)
            formatted = f"{state_name} ({raw_format})"
        else:
            # Use the normal formatting
            formatter = _FIELD_CACHE.get_formatter(self.field_config, field_name)
            formatted = formatter(value)

        # Include active bit range in display if not the full field
        active_bits = _FIELD_CACHE.get_active_bits(self.field_config, field_name)
        bits = _FIELD_CACHE.get_bits(self.field_config, field_name)

        msb, lsb = active_bits
        if msb != bits - 1 or lsb != 0:
            # Only show bit range if it's not the full field
            if msb == lsb:
                formatted = f"{formatted}[{msb}]"
            else:
                formatted = f"{formatted}[{msb}:{lsb}]"

        return formatted

    def __str__(self):
        """
        Provide a detailed string representation of the packet.
        Fields are displayed in the order they were defined in the field_config.

        Returns:
            Formatted string with all fields
        """
        result = [f"{self.__class__.__name__}:"]

        # Find the longest field description for alignment
        max_desc_len = max(
            len(field_def.description)
            for field_def in self.field_config.fields()
        )

        # Add all fields with their formatted values
        for field_name, field_def in self.field_config.items():
            value = self.fields[field_name]
            description = field_def.description
            formatted_value = self._format_field(field_name, value)

            # Pad the description to align values
            padded_desc = description.ljust(max_desc_len)
            result.append(f"  {padded_desc}: {formatted_value}")

            # If this is a partial field, also show the FIFO value
            active_bits = _FIELD_CACHE.get_active_bits(self.field_config, field_name)
            if active_bits[1] > 0 and value != -1:  # Skip FIFO display for X/Z values
                fifo_value = self.shift_for_fifo(value, field_name)
                fifo_formatted = self._format_field(field_name, fifo_value)
                result.append(f"  {' ' * max_desc_len}  FIFO: {fifo_formatted}")

        # Add timing information if available
        if self.start_time > 0:
            result.append(f"  Start Time: {self.start_time} ns")
        if self.end_time > 0:
            result.extend(
                (
                    f"  End Time: {self.end_time} ns",
                    f"  Duration: {self.end_time - self.start_time} ns",
                )
            )
        return "\n".join(result)

    def formatted(self, compact=False, show_fifo=False):
        """
        Return a formatted string representation.

        Args:
            compact: If True, return a more compact representation
            show_fifo: If True, show FIFO values instead of full field values

        Returns:
            Formatted string representation
        """
        if not compact:
            # Use the full string representation
            return self.__str__()

        # Compact representation with just field values
        fields = []
        for field_name, field_def in self.field_config.items():
            value = self.fields[field_name]
            if show_fifo and value != -1:  # Skip FIFO calculation for X/Z values
                value = self.shift_for_fifo(value, field_name)
            formatted_value = self._format_field(field_name, value)
            fields.append(f"{field_name}={formatted_value}")
        return f"{self.__class__.__name__}({', '.join(fields)})"

    def __eq__(self, other):
        """
        Compare packets for equality, skipping fields in skip_compare_fields.
        Also checks for undefined values (X/Z), which are typically represented as -1.

        Args:
            other: Another packet to compare with

        Returns:
            True if all non-skipped fields match and have defined values, False otherwise
        """
        if not isinstance(other, Packet):
            return NotImplemented

        # Compare all non-skipped fields
        for field_name in self.field_config.field_names():
            # Skip fields that are configured to be skipped during comparison
            if field_name in self.skip_compare_fields:
                continue

            # Check if field exists in both packets
            if field_name not in self.fields or field_name not in other.fields:
                return False

            self_value = self.fields[field_name]
            other_value = other.fields[field_name]

            # Check for undefined values (X/Z represented as -1 in simulation)
            if self_value == -1 or other_value == -1:
                return False  # Undefined values should cause comparison to fail

            # Check if values match
            if self_value != other_value:
                return False

        return True

    def copy(self):
        """
        Create a copy of this packet.

        Returns:
            New packet with the same field values
        """
        # Create new packet with same field config
        new_packet = self.__class__(self.field_config, self.skip_compare_fields)

        # Copy field values
        for field_name, value in self.fields.items():
            new_packet.fields[field_name] = value

        # Copy timing information
        new_packet.start_time = self.start_time
        new_packet.end_time = self.end_time

        return new_packet
