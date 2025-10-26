# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MemoryModel
# Purpose: Memory Model Class with Integrated Diagnostics and Access Tracking
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Memory Model Class with Integrated Diagnostics and Access Tracking

This module provides a high-performance memory model with comprehensive diagnostics,
access tracking, and region management capabilities for hardware verification.
"""
import numpy as np
from typing import Optional, Dict, Any, Union, List, Tuple


class MemoryModel:
    """
    Memory model with integrated diagnostics, access tracking, and region management.

    Provides high-performance memory operations using NumPy with comprehensive
    debugging capabilities, boundary checking, and memory organization features.
    """

    def __init__(self, num_lines, bytes_per_line, log=None, preset_values=None, debug=False):
        """
        Initialize the memory model.

        Args:
            num_lines: Number of memory lines
            bytes_per_line: Bytes per memory line
            log: Logger instance
            preset_values: Optional initial values for memory
            debug: Enable detailed debug logging
        """
        self.num_lines = num_lines
        self.bytes_per_line = bytes_per_line
        self.size = num_lines * bytes_per_line
        self.log = log
        self.debug = debug

        # Initialize memory using numpy for better performance
        if preset_values:
            if len(preset_values) != self.size:
                if log:
                    log.warning(f"Preset values length {len(preset_values)} doesn't match memory size {self.size}. Adjusting.")

                # Truncate or pad preset values to match memory size
                if len(preset_values) > self.size:
                    preset_values = preset_values[:self.size]
                else:
                    preset_values = preset_values + [0] * (self.size - len(preset_values))

            # Convert to numpy array
            self.mem = np.frombuffer(bytearray(preset_values), dtype=np.uint8).copy()
            self.preset_values = np.frombuffer(bytearray(preset_values), dtype=np.uint8).copy()
        else:
            self.mem = np.zeros(self.size, dtype=np.uint8)
            self.preset_values = np.zeros(self.size, dtype=np.uint8)

        # Access tracking for diagnostics
        self.read_access_map = np.zeros(self.size, dtype=np.uint32)  # Count reads per address
        self.write_access_map = np.zeros(self.size, dtype=np.uint32)  # Count writes per address

        # Memory regions for logical organization
        self.regions = {}  # name -> (start_addr, end_addr, description)

        # Statistics
        self.stats = {
            'reads': 0,
            'writes': 0,
            'read_errors': 0,
            'write_errors': 0,
            'uninitialized_reads': 0,
            'boundary_violations': 0,
            'overflow_masked': 0
        }

    def write(self, address, data, strobe=None):
        """
        Write data to memory with improved error handling and diagnostics.

        Args:
            address: Target memory address
            data: Data to write (bytearray)
            strobe: Optional write strobe (bit mask for byte enables)

        Raises:
            ValueError: If address or data is invalid
            IndexError: If write would exceed memory bounds
        """
        if not isinstance(data, bytearray):
            raise TypeError("Data must be a bytearray")

        # Set default strobe if not provided (all bytes enabled)
        if strobe is None:
            strobe = (1 << len(data)) - 1

        start = address
        data_len = len(data)
        end = start + data_len

        # Check for memory overflow
        if end > self.size:
            self.stats['boundary_violations'] += 1
            raise ValueError(f"Write at address 0x{address:X} with size {data_len} exceeds memory bounds (size: {self.size})")

        # Ensure the data and strobe lengths match
        if data_len * 8 < strobe.bit_length():
            raise ValueError(f"Data length {data_len} does not match strobe length {strobe.bit_length() // 8}")

        # Format the address and data as hexadecimal for debugging
        if self.debug and self.log:
            hex_address = f"0x{address:08X}"
            hex_data = [f"0x{byte:02X}" for byte in data]
            self.log.debug(f"Writing to memory: address={hex_address}, data={hex_data}, strobe={strobe:08b}")

        # Convert bytearray to numpy array
        data_np = np.frombuffer(data, dtype=np.uint8)

        # Create a mask array from the strobe
        mask = np.zeros(data_len, dtype=bool)
        for i in range(data_len):
            if strobe & (1 << i):
                mask[i] = True

                # Update write access map
                self.write_access_map[start + i] += 1

                if self.debug and self.log:
                    self.log.debug(f"Writing byte: mem[{start+i:08X}] = {data_np[i]:02X}")

        # Apply the masked write operation in one vectorized operation
        if np.any(mask):
            indices = np.arange(start, start + data_len)[mask]
            self.mem[indices] = data_np[mask]

            # Update statistics
            self.stats['writes'] += 1

    def read(self, address, length):
        """
        Read data from memory with error checking and access tracking.

        Args:
            address: Memory address to read from
            length: Number of bytes to read

        Returns:
            Bytearray containing the read data

        Raises:
            ValueError: If address or length is invalid
            IndexError: If read would exceed memory bounds
        """
        # Check for memory overflow
        if address + length > self.size:
            self.stats['boundary_violations'] += 1
            raise ValueError(f"Read at address 0x{address:X} with size {length} exceeds memory bounds (size: {self.size})")

        # Update read access map
        for i in range(length):
            self.read_access_map[address + i] += 1

            # Check for uninitialized memory (if all preset values were zero)
            if np.all(self.preset_values == 0) and self.write_access_map[address + i] == 0:
                if self.log:
                    self.log.warning(f"Reading uninitialized memory at address 0x{address + i:X}")
                self.stats['uninitialized_reads'] += 1

        # Update statistics
        self.stats['reads'] += 1

        # Read the data
        data = self.mem[address:address + length].copy()

        # Convert back to bytearray to maintain API compatibility
        return bytearray(data)

    def reset(self, to_preset=False):
        """
        Reset memory to initial state.

        Args:
            to_preset: If True, reset to preset values; if False, reset to all zeros
        """
        if to_preset:
            self.mem = self.preset_values.copy()
        else:
            self.mem = np.zeros(self.size, dtype=np.uint8)

        # Reset access maps
        self.read_access_map.fill(0)
        self.write_access_map.fill(0)

        # Reset statistics
        for key in self.stats:
            self.stats[key] = 0

    def expand(self, additional_lines):
        """
        Expand memory by adding additional lines.

        Args:
            additional_lines: Number of lines to add
        """
        additional_size = additional_lines * self.bytes_per_line

        # Expand memory
        self.mem = np.append(self.mem, np.zeros(additional_size, dtype=np.uint8))
        self.preset_values = np.append(self.preset_values, np.zeros(additional_size, dtype=np.uint8))

        # Expand access maps
        self.read_access_map = np.append(self.read_access_map, np.zeros(additional_size, dtype=np.uint32))
        self.write_access_map = np.append(self.write_access_map, np.zeros(additional_size, dtype=np.uint32))

        # Update memory dimensions
        self.num_lines += additional_lines
        self.size += additional_size

    def define_region(self, name, start_addr, end_addr, description=None):
        """
        Define a named memory region for better organization and diagnostics.

        Args:
            name: Region name
            start_addr: Starting address (inclusive)
            end_addr: Ending address (inclusive)
            description: Optional description of the region

        Returns:
            Self for method chaining
        """
        # Validate region
        if end_addr < start_addr:
            if self.log:
                self.log.warning(f"Invalid region '{name}': end_addr {end_addr} < start_addr {start_addr}")
            return self

        if start_addr < 0 or end_addr >= self.size:
            if self.log:
                self.log.warning(f"Invalid region '{name}': addresses out of bounds (0-{self.size-1})")
            return self

        # Store region
        self.regions[name] = (start_addr, end_addr, description or name)

        if self.log:
            self.log.info(f"Defined memory region '{name}': 0x{start_addr:X}-0x{end_addr:X} ({description or name})")

        return self

    def get_region_access_stats(self, name):
        """
        Get access statistics for a named region.

        Args:
            name: Region name

        Returns:
            Dictionary with region access statistics
        """
        if name not in self.regions:
            return None

        start_addr, end_addr, _ = self.regions[name]
        size = end_addr - start_addr + 1

        reads = np.sum(self.read_access_map[start_addr:end_addr + 1])
        writes = np.sum(self.write_access_map[start_addr:end_addr + 1])

        return {
            'region': name,
            'start_addr': start_addr,
            'end_addr': end_addr,
            'size': size,
            'total_reads': int(reads),
            'total_writes': int(writes),
            'read_percentage': int(reads) / size if size > 0 else 0,
            'write_percentage': int(writes) / size if size > 0 else 0,
            'untouched_addresses': int(np.sum((self.read_access_map[start_addr:end_addr + 1] == 0) &
                                            (self.write_access_map[start_addr:end_addr + 1] == 0)))
        }

    def write_transaction(self, transaction, check_required_fields=True, component_name="Component"):
        """
        Write transaction data to memory with error handling (integrated from FIFOMemoryInteg).

        Args:
            transaction: The transaction to write to memory
            check_required_fields: If True, validate that required fields exist
            component_name: Component name for error messages

        Returns:
            (success, error_message): Tuple with success flag and error message
        """
        try:
            # Default field mapping
            addr_field = getattr(transaction, 'addr', 0) if hasattr(transaction, 'addr') else 0
            data_field = getattr(transaction, 'data', 0) if hasattr(transaction, 'data') else 0
            strb_field = getattr(transaction, 'strb', None) if hasattr(transaction, 'strb') else None

            # Check if transaction has required fields
            if check_required_fields:
                if not hasattr(transaction, 'addr'):
                    return False, f"Transaction missing required address field"
                if not hasattr(transaction, 'data'):
                    return False, f"Transaction missing required data field"

            addr = addr_field
            data = data_field

            # Get strobe if available, default to all bytes enabled
            if strb_field is not None:
                strb = strb_field
            else:
                strb = (1 << self.bytes_per_line) - 1

            # Perform boundary checking
            if addr < 0:
                self.stats['boundary_violations'] += 1
                return False, f"Invalid negative address: {addr}"

            if addr + self.bytes_per_line > self.size:
                self.stats['boundary_violations'] += 1
                return False, f"Memory write at 0x{addr:X} would exceed memory bounds (size: {self.size})"

            # Convert data to bytearray with proper size handling
            try:
                data_bytes = self.integer_to_bytearray(data, self.bytes_per_line)
            except OverflowError:
                # If data doesn't fit, mask it
                max_value = (1 << (self.bytes_per_line * 8)) - 1
                masked_data = data & max_value
                if self.log:
                    self.log.warning(
                        f"{component_name}: Data value 0x{data:X} exceeds memory width, masked to 0x{masked_data:X}"
                    )
                data_bytes = self.integer_to_bytearray(masked_data, self.bytes_per_line)
                self.stats['overflow_masked'] += 1

            # Write to memory
            self.write(addr, data_bytes, strb)
            if self.log:
                self.log.debug(f"{component_name}: Wrote to memory: addr=0x{addr:X}, data=0x{data:X}, strb=0x{strb:X}")

            return True, ""

        except Exception as e:
            error_msg = f"{component_name}: Error writing to memory: {str(e)}"
            if self.log:
                self.log.error(error_msg)
            self.stats['write_errors'] += 1
            return False, error_msg

    def read_transaction(self, transaction, update_transaction=True, check_required_fields=True, component_name="Component"):
        """
        Read data from memory based on transaction address (integrated from FIFOMemoryInteg).

        Args:
            transaction: The transaction containing the address to read from
            update_transaction: If True, update the transaction's data field with read value
            check_required_fields: If True, validate that required fields exist
            component_name: Component name for error messages

        Returns:
            (success, data, error_message): Tuple with success flag, data read (or None), and error message
        """
        try:
            # Check if transaction has required fields
            if check_required_fields and not hasattr(transaction, 'addr'):
                return False, None, f"Transaction missing required address field"

            # Get address from transaction
            addr = getattr(transaction, 'addr', 0)

            # Perform boundary checking
            if addr < 0:
                self.stats['boundary_violations'] += 1
                return False, None, f"Invalid negative address: {addr}"

            if addr + self.bytes_per_line > self.size:
                self.stats['boundary_violations'] += 1
                return False, None, f"Memory read at 0x{addr:X} would exceed memory bounds (size: {self.size})"

            # Read from memory
            data_bytes = self.read(addr, self.bytes_per_line)
            data = self.bytearray_to_integer(data_bytes)

            # Update transaction if requested
            if update_transaction and hasattr(transaction, 'data'):
                setattr(transaction, 'data', data)

            if self.log:
                self.log.debug(f"{component_name}: Read from memory: addr=0x{addr:X}, data=0x{data:X}")

            return True, data, ""

        except Exception as e:
            error_msg = f"{component_name}: Error reading from memory: {str(e)}"
            if self.log:
                self.log.error(error_msg)
            self.stats['read_errors'] += 1
            return False, None, error_msg

    def dump(self, include_access_info=False):
        """
        Generate a detailed memory dump.

        Args:
            include_access_info: If True, include read/write access information

        Returns:
            String with the memory dump
        """
        mem_dump = "-" * 60 + '\n'

        # Add header
        mem_dump += f"Memory Dump: {self.num_lines} lines x {self.bytes_per_line} bytes = {self.size} bytes\n"
        mem_dump += "-" * 60 + '\n'

        # Dump memory contents by line
        for i in range(self.num_lines):
            addr = i * self.bytes_per_line

            # Get memory line data
            line_data = bytes(self.mem[addr:addr + self.bytes_per_line])
            value = int.from_bytes(line_data, byteorder='little')

            # Format line with address and value
            mem_dump += f"Line {i:4}: Address 0x{addr:08X} - Value 0x{value:0{self.bytes_per_line * 2}X}"

            # Add access info if requested
            if include_access_info:
                reads = np.sum(self.read_access_map[addr:addr + self.bytes_per_line])
                writes = np.sum(self.write_access_map[addr:addr + self.bytes_per_line])
                mem_dump += f" (Reads: {reads}, Writes: {writes})"

            mem_dump += '\n'

        # Add region information if any regions defined
        if self.regions:
            mem_dump += "\nMemory Regions:\n"
            mem_dump += "-" * 60 + '\n'

            for name, (start, end, desc) in self.regions.items():
                stats = self.get_region_access_stats(name)
                mem_dump += f"Region '{name}': 0x{start:X}-0x{end:X} ({desc})\n"
                if stats:
                    mem_dump += f"  Size: {stats['size']} bytes, Reads: {stats['total_reads']}, Writes: {stats['total_writes']}\n"
                    mem_dump += f"  Untouched: {stats['untouched_addresses']} bytes ({stats['untouched_addresses'] * 100 / stats['size']:.1f}%)\n"

        mem_dump += "-" * 60 + '\n'
        return '\n' + mem_dump

    def get_stats(self):
        """
        Get comprehensive memory operation statistics.

        Returns:
            Dictionary with statistics including coverage information
        """
        # Calculate additional statistics
        coverage = {
            'read_coverage': np.count_nonzero(self.read_access_map) / self.size,
            'write_coverage': np.count_nonzero(self.write_access_map) / self.size,
            'any_access_coverage': np.count_nonzero(self.read_access_map | self.write_access_map) / self.size,
            'untouched_bytes': np.count_nonzero((self.read_access_map == 0) & (self.write_access_map == 0))
        }

        return {**self.stats, **coverage}

    def integer_to_bytearray(self, value, byte_length=None):
        """
        Convert an integer to a bytearray with error checking.

        Args:
            value: Integer value to convert
            byte_length: Length of resulting bytearray

        Returns:
            Bytearray representation of the value

        Raises:
            TypeError: If value is not an integer
            ValueError: If value is negative
            OverflowError: If value is too large for the specified byte_length
        """
        # Ensure value is a valid integer
        if not isinstance(value, int):
            raise TypeError("Value must be an integer")

        if value < 0:
            raise ValueError("Negative integers are not supported for conversion")

        # Calculate byte_length if not provided
        if byte_length is None:
            byte_length = (value.bit_length() + 7) // 8
            byte_length = max(1, byte_length)  # Ensure at least 1 byte

        # Check if the value can fit into the specified byte_length
        max_value = (1 << (byte_length * 8)) - 1
        if value > max_value:
            raise OverflowError(
                f"Value {value} is too large to fit into {byte_length} bytes. "
                f"Maximum allowed value is {max_value}."
            )

        # Perform the conversion
        return bytearray(value.to_bytes(byte_length, byteorder='little'))

    def bytearray_to_integer(self, byte_array):
        """
        Convert a bytearray to an integer.

        Args:
            byte_array: Bytearray to convert

        Returns:
            Integer representation of the bytearray
        """
        return int.from_bytes(byte_array, byteorder='little')
