# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FIFOSequence
# Purpose: FIFO Sequence - CLEANED VERSION
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
FIFO Sequence - CLEANED VERSION

Simplified sequence generator focused on core pattern generation functionality.
Removes complex dependency tracking and FIFO modeling that belongs in components.

Key improvements:
- Simple transaction list instead of complex dependency graphs
- Focus on pattern generation (incremental, walking bits, random, etc.)
- Leverages existing PacketFactory and FieldConfig infrastructure
- Clean factory methods for common test patterns
- Eliminates unnecessary complexity while keeping useful features
"""
import random
from typing import Dict, List, Optional, Tuple, Any

from ..shared.field_config import FieldConfig
from ..shared.packet_factory import PacketFactory
from .fifo_packet import FIFOPacket


class FIFOSequence:
    """
    Simplified FIFO sequence generator focused on core functionality.

    Removes complex dependency tracking and FIFO modeling that belongs
    in the actual components, not the sequence generator.
    """

    def __init__(self, name="basic", field_config=None, packet_class=FIFOPacket, log=None):
        """Initialize the FIFO sequence."""
        self.name = name
        self.packet_class = packet_class
        self.log = log

        # Handle field_config conversion
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        elif field_config is None:
            self.field_config = FieldConfig.create_data_only()
        else:
            self.field_config = field_config

        # Create packet factory
        self.packet_factory = PacketFactory(packet_class, self.field_config)

        # Sequence data - simplified
        self.transactions = []  # List of (field_values, delay) tuples

        # Randomization
        self.use_random_selection = False
        self.master_randomizer = None
        self.slave_randomizer = None

        if self.log:
            self.log.info(f"FIFOSequence '{name}' initialized")

    def add_transaction(self, field_values=None, delay=0):
        """Add a transaction to the sequence."""
        field_values = field_values or {}
        self.transactions.append((field_values, delay))

        if self.log:
            self.log.debug(f"Added transaction {len(self.transactions)-1}: {field_values}")

        return len(self.transactions) - 1  # Return index

    def add_data_value(self, data, delay=0):
        """Add a transaction with a data value."""
        return self.add_transaction({'data': data}, delay)

    def set_randomizers(self, master_randomizer=None, slave_randomizer=None):
        """Set randomizers for timing control."""
        if master_randomizer:
            self.master_randomizer = master_randomizer
        if slave_randomizer:
            self.slave_randomizer = slave_randomizer
        return self

    def set_random_selection(self, enable=True):
        """Enable/disable random selection from sequences."""
        self.use_random_selection = enable
        return self

    def set_fifo_parameters(self, capacity=8, back_pressure=0.0):
        """
        Set FIFO-specific parameters for more realistic sequence generation.

        Args:
            capacity: FIFO capacity in entries
            back_pressure: Probability of back-pressure (0.0 to 1.0)

        Returns:
            Self for method chaining
        """
        self.fifo_capacity = capacity
        self.back_pressure = max(0.0, min(1.0, back_pressure))  # Clamp to [0.0, 1.0]
        return self

    def generate_packets(self, count=None, apply_fifo_metadata=True):
        """
        Generate packets from the sequence.

        Args:
            count: Number of packets to generate (None = all transactions)
            apply_fifo_metadata: Whether to apply FIFO metadata (kept for compatibility)

        Returns:
            List of generated packets
        """
        packets = []

        # Determine how many transactions to process
        transactions_to_process = self.transactions
        if count is not None and count < len(self.transactions):
            transactions_to_process = self.transactions[:count]

        for field_values, delay in transactions_to_process:
            # Use PacketFactory
            packet = self.packet_factory.create_packet(**field_values)

            # Apply randomizers if available
            if self.master_randomizer:
                packet.set_master_randomizer(self.master_randomizer)
            if self.slave_randomizer:
                packet.set_slave_randomizer(self.slave_randomizer)

            # Store delay in packet for command handler to use
            packet.sequence_delay = delay

            packets.append(packet)

        if self.log:
            self.log.info(f"Generated {len(packets)} packets for sequence '{self.name}'")

        return packets

    # Simplified pattern generation methods
    def add_data_incrementing(self, count, start=0, step=1, delay=0):
        """Add incrementing data pattern."""
        for i in range(count):
            self.add_data_value(start + (i * step), delay)
        return self

    def add_walking_ones(self, data_width=32, delay=0):
        """Add walking ones pattern."""
        for bit in range(data_width):
            self.add_data_value(1 << bit, delay)
        return self

    def add_walking_zeros(self, data_width=32, delay=0):
        """Add walking zeros pattern."""
        # Get max value based on field configuration
        if self.field_config.has_field('data'):
            field_width = self.field_config.get_field('data').bits
            max_val = (1 << field_width) - 1
        else:
            max_val = (1 << data_width) - 1

        for bit in range(data_width):
            self.add_data_value(max_val & ~(1 << bit), delay)
        return self

    def add_random_data(self, count, delay=0):
        """Add random data pattern."""
        for _ in range(count):
            self.add_data_value(random.randint(0, 0xFFFFFFFF), delay)
        return self

    def add_corner_cases(self, delay=0):
        """Add common corner case values."""
        corner_values = [0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA]
        for value in corner_values:
            self.add_data_value(value, delay)
        return self

    def clear(self):
        """Clear the sequence."""
        self.transactions.clear()
        if self.log:
            self.log.info(f"Cleared sequence '{self.name}'")

    # Simplified factory methods
    @classmethod
    def create_burst(cls, name="burst", count=10, start=0x1000, log=None):
        """Create a simple burst sequence."""
        sequence = cls(name, log=log)
        sequence.add_data_incrementing(count, start=start, step=1, delay=0)
        return sequence

    @classmethod
    def create_pattern_test(cls, name="patterns", data_width=32, log=None):
        """Create a sequence with common test patterns."""
        sequence = cls(name, log=log)

        # Basic patterns
        sequence.add_data_incrementing(8, start=0x1000, step=1, delay=0)
        sequence.add_walking_ones(min(data_width, 16), delay=0)
        sequence.add_walking_zeros(min(data_width, 16), delay=0)
        sequence.add_random_data(10, delay=0)
        sequence.add_corner_cases(delay=0)

        return sequence

    @classmethod
    def create_stress_test(cls, name="stress", count=50, burst_size=10, log=None):
        """Create a stress test with bursts and gaps."""
        sequence = cls(name, log=log)

        current_data = 0x8000
        for i in range(0, count, burst_size):
            # Add burst
            burst_count = min(burst_size, count - i)
            for j in range(burst_count):
                # No delay within burst, small delay between bursts
                delay = 2 if j == burst_count - 1 and i + burst_count < count else 0
                sequence.add_data_value(current_data, delay)
                current_data += 1

        return sequence

    @classmethod
    def create_data_stress_test(cls, name="data_stress", data_width=32, delay=1, log=None):
        """
        Create a comprehensive data stress test sequence.

        Args:
            name: Sequence name
            data_width: Width of data in bits
            delay: Delay between pattern groups
            log: Logger instance

        Returns:
            Configured FIFOSequence for stress testing data patterns
        """
        sequence = cls(name, log=log)

        # Add walking patterns
        sequence.add_walking_ones(data_width, delay=0)
        sequence.add_walking_zeros(data_width, delay=0)

        # Add corner values
        sequence.add_data_value(0x00000000, delay=0)  # All zeros
        sequence.add_data_value(0xFFFFFFFF, delay=0)  # All ones (will be masked by Packet)
        sequence.add_data_value(0x55555555, delay=0)  # Alternating
        sequence.add_data_value(0xAAAAAAAA, delay=0)  # Alternating

        # Add random values
        sequence.add_random_data(10, delay=0)

        # Add some delayed transactions for timing variation
        for i in range(5):
            sequence.add_data_value(0x9000 + i, delay=delay)

        if log:
            log.info(f"Created data stress test sequence '{name}' with data_width={data_width}")

        return sequence

    @classmethod
    def create_comprehensive_test(cls, name="comprehensive", field_config=None,
                                 packets_per_pattern=10, data_width=32,
                                 capacity=None, include_dependencies=True, log=None):
        """
        Create a comprehensive test sequence with multiple patterns.

        Args:
            name: Sequence name
            field_config: Field configuration to use
            packets_per_pattern: Number of packets per test pattern
            data_width: Data width for patterns
            capacity: FIFO capacity for testing (optional)
            include_dependencies: Whether to include dependency tests
            log: Logger instance
        """
        sequence = cls(name, field_config=field_config, log=log)

        # Multiple test patterns
        sequence.add_data_incrementing(packets_per_pattern, start=0x1000, step=1, delay=0)
        sequence.add_walking_ones(min(data_width, packets_per_pattern), delay=0)
        sequence.add_walking_zeros(min(data_width, packets_per_pattern), delay=0)
        sequence.add_random_data(packets_per_pattern, delay=0)
        sequence.add_corner_cases(delay=0)

        # Add some delayed transactions for timing variation
        for i in range(5):
            sequence.add_data_value(0x5000 + i, delay=i + 1)

        # Add capacity-related patterns if capacity is specified
        if capacity is not None and capacity > 0:
            # Add burst that approaches capacity
            burst_size = max(1, capacity - 2)
            sequence.add_data_incrementing(burst_size, start=0x6000, step=1, delay=0)

            # Add gap and then another burst
            sequence.add_data_value(0x7000, delay=capacity // 2)
            sequence.add_data_incrementing(capacity, start=0x8000, step=1, delay=0)

        # Add dependency-like patterns if requested (simplified version using delays)
        if include_dependencies:
            for i in range(min(5, packets_per_pattern)):
                sequence.add_data_value(0x9000 + i, delay=i + 1)

        if log:
            log.info(f"Created comprehensive test sequence '{name}' with {len(sequence.transactions)} transactions, "
                    f"data_width={data_width}, capacity={capacity}")

        return sequence

    @classmethod
    def create_mixed_patterns(cls, name="mixed", pattern_size=8, log=None):
        """Create a sequence with mixed test patterns."""
        sequence = cls(name, log=log)

        # Pattern 1: Incremental
        sequence.add_data_incrementing(pattern_size, start=0x0100, step=1, delay=0)

        # Pattern 2: Powers of 2
        for i in range(min(pattern_size, 32)):
            sequence.add_data_value(1 << i, delay=0)

        # Pattern 3: Fibonacci-like sequence
        a, b = 1, 1
        for i in range(pattern_size):
            sequence.add_data_value(a & 0xFFFFFFFF, delay=0)
            a, b = b, a + b

        # Pattern 4: Alternating high/low
        for i in range(pattern_size):
            if i % 2 == 0:
                sequence.add_data_value(0x0000FFFF, delay=0)
            else:
                sequence.add_data_value(0xFFFF0000, delay=0)

        return sequence

    @classmethod
    def create_dependency_chain(cls, name="dependency_chain", count=5,
                               data_start=0, data_step=1, delay=0, log=None):
        """
        Create a sequence with simple dependency chain (simplified version).

        This is a simplified version that creates a basic sequence with delays
        instead of complex dependency tracking. The delay provides the timing
        relationship between transactions.

        Args:
            name: Sequence name
            count: Number of transactions
            data_start: Starting data value
            data_step: Step size between data values
            delay: Delay between transactions (simulates dependency timing)
            log: Logger instance

        Returns:
            Configured FIFOSequence instance
        """
        sequence = cls(name, log=log)

        # First transaction with no delay
        if count > 0:
            sequence.add_data_value(data_start, delay=0)

        # Remaining transactions with delays (simulates dependency waiting)
        for i in range(1, count):
            data_value = data_start + (i * data_step)
            sequence.add_data_value(data_value, delay=delay)

        if log:
            log.info(f"Created dependency chain sequence '{name}' with {count} transactions")

        return sequence

    @classmethod
    def create_capacity_test(cls, name="capacity_test", capacity=8, log=None):
        """
        Create a test sequence designed to test FIFO capacity limits.

        Args:
            name: Sequence name
            capacity: FIFO capacity to test
            log: Logger instance

        Returns:
            Configured FIFOSequence for capacity testing
        """
        sequence = cls(name, log=log)

        # Test 1: Fill exactly to capacity
        sequence.add_data_incrementing(capacity, start=0x1000, step=1, delay=0)

        # Test 2: Try to overfill (capacity + 2) with small delays
        for i in range(capacity + 2):
            sequence.add_data_value(0x2000 + i, delay=1 if i >= capacity else 0)

        # Test 3: Burst patterns
        burst_size = max(1, capacity // 2)
        for i in range(3):  # 3 bursts
            for j in range(burst_size):
                sequence.add_data_value(0x3000 + (i * 0x100) + j, delay=0)
            # Gap between bursts
            if i < 2:
                sequence.add_data_value(0x4000 + i, delay=capacity // 2)

        if log:
            log.info(f"Created capacity test sequence '{name}' for capacity={capacity}")

        return sequence

    @classmethod
    def create_corner_case_test(cls, name="corner_cases", field_config=None, log=None):
        """
        Create a sequence focused on corner case testing.

        Args:
            name: Sequence name
            field_config: Field configuration to use
            log: Logger instance

        Returns:
            Configured FIFOSequence with corner case patterns
        """
        sequence = cls(name, field_config=field_config, log=log)

        if field_config and len(field_config.field_names()) > 1:
            # Multi-field corner cases
            field_names = field_config.field_names()

            # All zeros
            zero_values = {fname: 0 for fname in field_names}
            sequence.add_transaction(zero_values, delay=0)

            # All max values
            max_values = {}
            for fname in field_names:
                if field_config.has_field(fname):
                    field_def = field_config.get_field(fname)
                    max_values[fname] = (1 << field_def.bits) - 1
            sequence.add_transaction(max_values, delay=0)

            # Alternating patterns
            for i in range(4):
                alt_values = {}
                for fname in field_names:
                    if field_config.has_field(fname):
                        field_def = field_config.get_field(fname)
                        if i % 2 == 0:
                            alt_values[fname] = 0x55555555 & ((1 << field_def.bits) - 1)
                        else:
                            alt_values[fname] = 0xAAAAAAAA & ((1 << field_def.bits) - 1)
                sequence.add_transaction(alt_values, delay=0)
        else:
            # Simple data-only corner cases
            corner_values = [
                0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA,
                0x12345678, 0x87654321, 0xDEADBEEF, 0xCAFEBABE
            ]
            for value in corner_values:
                sequence.add_data_value(value, delay=0)

        if log:
            log.info(f"Created corner case test sequence '{name}'")

        return sequence

    # Backward compatibility methods that existing tests might expect
    def get_dependency_graph(self):
        """
        Get a simple representation of transaction dependencies (simplified).

        Returns a minimal dependency graph for backward compatibility.
        Since we simplified away complex dependency tracking, this returns
        a basic structure that existing code can handle.
        """
        return {
            'dependencies': {},  # No complex dependencies in simplified version
            'dependency_types': {},
            'transaction_count': len(self.transactions)
        }

    def get_stats(self):
        """Get simple statistics."""
        return {
            'sequence_name': self.name,
            'transaction_count': len(self.transactions),
            'random_selection': self.use_random_selection,
            'has_master_randomizer': self.master_randomizer is not None,
            'has_slave_randomizer': self.slave_randomizer is not None
        }

    def __len__(self):
        """Return number of transactions."""
        return len(self.transactions)

    def __str__(self):
        return f"FIFOSequence '{self.name}': {len(self.transactions)} transactions"

    def __repr__(self):
        return f"FIFOSequence(name='{self.name}', transactions={len(self.transactions)})"

    @classmethod
    def create_fifo_capacity_test(cls, name="capacity_test", capacity=8):
        """
        Create a sequence specifically designed to test FIFO capacity boundaries.

        Args:
            name: Sequence name
            capacity: Target FIFO capacity to test

        Returns:
            Configured FIFOSequence instance
        """
        sequence = cls(name)
        sequence.set_fifo_parameters(capacity=capacity)

        # Add capacity+1 incrementing values to test overflow behavior
        sequence.add_data_incrementing(capacity + 1, start=0xA0, step=1, delay=0)

        # Add sequence to test empty condition
        sequence.add_data_incrementing(capacity, start=0xB0, step=1, delay=2)

        # Test underflow behavior (reading when empty)
        sequence.add_data_value(0xBF, delay=0)

        # Add almost-full test
        sequence.add_data_incrementing(capacity - 1, start=0xC0, step=1, delay=0)

        # Add alternate filling/emptying patterns
        for i in range(3):
            # Fill halfway
            offset = 0xD0 + (i * 0x10)
            sequence.add_data_incrementing(capacity // 2, start=offset, step=1, delay=0)

            # Fill completely
            sequence.add_data_incrementing(capacity // 2, start=offset + (capacity // 2), step=1, delay=0)

        return sequence
