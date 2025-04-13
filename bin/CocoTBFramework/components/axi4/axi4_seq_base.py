"""
AXI4 Base Sequence

This module provides a base class for all AXI4 sequence classes, with
common functionality for randomization, memory management, and utility methods.
"""

from typing import Dict, List, Any, Optional, Union, Callable, Tuple, Set
from dataclasses import dataclass, field
import weakref
import gc
import logging

from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.randomization_config import RandomizationConfig, RandomizationMode


class AXI4BaseSequence:
    """
    Base class for all AXI4 sequence classes.

    This class provides common functionality for:
    1. Randomization management with configurable strategies
    2. Memory management to prevent leaks
    3. Utility functions for protocol-specific operations
    4. Common statistics tracking

    All AXI4 sequence classes should inherit from this base.
    """

    # Global registry of active sequences for cleanup
    _active_sequences = weakref.WeakSet()

    # AXI4 burst types
    BURST_FIXED = 0
    BURST_INCR = 1
    BURST_WRAP = 2

    # AXI4 response types
    RESP_OKAY = 0
    RESP_EXOKAY = 1
    RESP_SLVERR = 2
    RESP_DECERR = 3

    def __init__(self, name: str = "base_sequence",
                    randomization_config: Optional[RandomizationConfig] = None,
                    logger: Optional[logging.Logger] = None):
        """
        Initialize the base sequence.

        Args:
            name: Sequence name for identification
            randomization_config: Configuration for randomization
            logger: Optional logger for sequence activities
        """
        self.name = name
        self.randomization_config = randomization_config
        self.logger = logger or logging.getLogger(name)

        # Register with global active sequences set
        AXI4BaseSequence._active_sequences.add(self)

        # Statistics tracking
        self.stats = {
            'total_transactions': 0,
            'randomization_calls': 0,
            'warnings': 0,
            'errors': 0,
            'memory_usage': 0
        }

        # Track generated values for debugging
        self.last_generated_values = {}

    def get_random_value(self, field_name: str,
                        min_value: Optional[int] = None,
                        max_value: Optional[int] = None) -> Any:
        """
        Generate a random value for a field based on configuration.

        Args:
            field_name: Field name to randomize
            min_value: Optional minimum value override
            max_value: Optional maximum value override

        Returns:
            Generated random value
        """
        # Handle case where no randomization config is set
        if self.randomization_config is None:
            if min_value is not None and max_value is not None:
                # Use FlexRandomizer directly with simple constraints
                randomizer = FlexRandomizer({
                    field_name: {
                        "bins": [(min_value, max_value)],
                        "weights": [1.0]
                    }
                })
                values = randomizer.next()
                value = values.get(field_name, min_value)
            else:
                # Create a default FlexRandomizer
                randomizer = FlexRandomizer({})
                values = randomizer.next()
                value = 0  # Default value
        else:
            # Use the configured randomization
            value = self.randomization_config.generate_value(field_name)

            # Apply min/max overrides if provided
            if min_value is not None and value < min_value:
                value = min_value
            if max_value is not None and value > max_value:
                value = max_value

        # Track for statistics and debugging
        self.stats['randomization_calls'] += 1
        self.last_generated_values[field_name] = value

        return value

    def get_random_values(self, field_names: List[str]) -> Dict[str, Any]:
        """
        Generate multiple random values at once.

        Args:
            field_names: List of field names to randomize

        Returns:
            Dictionary mapping field names to generated values
        """
        if self.randomization_config:
            # Use batch generation if available
            return self.randomization_config.generate_values(field_names)

        # Otherwise generate one by one
        return {name: self.get_random_value(name) for name in field_names}

    def log_warning(self, message: str) -> None:
        """
        Log a warning with tracking.

        Args:
            message: Warning message to log
        """
        self.logger.warning(f"{self.name}: {message}")
        self.stats['warnings'] += 1

    def log_error(self, message: str) -> None:
        """
        Log an error with tracking.

        Args:
            message: Error message to log
        """
        self.logger.error(f"{self.name}: {message}")
        self.stats['errors'] += 1

    def log_info(self, message: str) -> None:
        """
        Log an info message.

        Args:
            message: Info message to log
        """
        self.logger.info(f"{self.name}: {message}")

    def cleanup(self) -> None:
        """
        Release resources to prevent memory leaks.
        This should be called when the sequence is no longer needed.

        Derived classes should override this method to clean up their
        specific resources, calling super().cleanup() at the end.
        """
        # Remove from global registry
        if self in AXI4BaseSequence._active_sequences:
            AXI4BaseSequence._active_sequences.remove(self)

        # Clear last generated values
        self.last_generated_values.clear()

    def __del__(self):
        """
        Destructor to ensure cleanup when the object is garbage collected.
        """
        self.cleanup()

    @classmethod
    def cleanup_all(cls) -> int:
        """
        Clean up all active sequences.
        Useful for preventing memory leaks between tests.

        Returns:
            Number of sequences cleaned up
        """
        count = len(cls._active_sequences)

        # Make a copy of the set as it will be modified during iteration
        for sequence in list(cls._active_sequences):
            sequence.cleanup()

        # Force a garbage collection cycle
        gc.collect()

        return count

    @staticmethod
    def get_burst_size_bytes(size: int) -> int:
        """
        Convert AXI burst size encoding to bytes.

        Args:
            size: AXI burst size (0=1 byte, 1=2 bytes, 2=4 bytes, etc.)

        Returns:
            Number of bytes per beat
        """
        if size < 0 or size > 7:  # Valid AXI sizes are 0-7
            raise ValueError(f"Invalid AXI burst size: {size}")

        return 1 << size  # 2^size

    @staticmethod
    def align_address(addr: int, size: int) -> int:
        """
        Align address to burst size boundary.

        Args:
            addr: Address to align
            size: AXI burst size (0=1 byte, 1=2 bytes, 2=4 bytes, etc.)

        Returns:
            Aligned address
        """
        bytes_per_beat = 1 << size
        return (addr // bytes_per_beat) * bytes_per_beat

    @staticmethod
    def is_power_of_two(n: int) -> bool:
        """
        Check if a number is a power of two.

        Args:
            n: Number to check

        Returns:
            True if n is a power of two, False otherwise
        """
        return n > 0 and (n & (n - 1)) == 0

    @staticmethod
    def next_power_of_two(n: int) -> int:
        """
        Find the next power of two greater than or equal to n.

        Args:
            n: Starting number

        Returns:
            Next power of two
        """
        if n <= 0:
            return 1

        # If already a power of two, return it
        if AXI4BaseSequence.is_power_of_two(n):
            return n

        # Find the next power of two
        n -= 1
        n |= n >> 1
        n |= n >> 2
        n |= n >> 4
        n |= n >> 8
        n |= n >> 16
        n += 1

        return n

    @staticmethod
    def calculate_burst_addresses(addr: int,
                                burst_len: int,
                                burst_size: int,
                                burst_type: int) -> List[int]:
        """
        Calculate all addresses in a burst according to AXI protocol rules.

        Args:
            addr: Starting address
            burst_len: Burst length (0=1 beat, 255=256 beats)
            burst_size: Burst size (0=1 byte, 1=2 bytes, 2=4 bytes, etc.)
            burst_type: Burst type (0=FIXED, 1=INCR, 2=WRAP)

        Returns:
            List of addresses for each beat in the burst
        """
        # Ensure address is aligned
        aligned_addr = AXI4BaseSequence.align_address(addr, burst_size)

        # Number of bytes per beat
        bytes_per_beat = 1 << burst_size

        # Number of beats in the burst
        num_beats = burst_len + 1

        # Generate addresses based on burst type
        addresses = []

        if burst_type == AXI4BaseSequence.BURST_FIXED:
            # FIXED burst - same address for all beats
            return [aligned_addr] * num_beats

        elif burst_type == AXI4BaseSequence.BURST_INCR:
            # INCR burst - increment address by bytes_per_beat
            addresses.extend(aligned_addr + i * bytes_per_beat for i in range(num_beats))
        elif burst_type == AXI4BaseSequence.BURST_WRAP:
            # WRAP burst - wrap at burst boundaries

            # Validate WRAP burst parameters
            if not AXI4BaseSequence.is_power_of_two(num_beats):
                raise ValueError(f"WRAP burst length+1 must be a power of 2, got {num_beats}")

            # Calculate wrap boundary
            wrap_size = num_beats * bytes_per_beat
            wrap_mask = wrap_size - 1
            wrap_boundary = aligned_addr & ~wrap_mask

            # Generate addresses
            for i in range(num_beats):
                offset = (aligned_addr + i * bytes_per_beat) & wrap_mask
                addresses.append(wrap_boundary + offset)

        else:
            raise ValueError(f"Invalid burst type: {burst_type}")

        return addresses

    @staticmethod
    def validate_burst_parameters(addr: int,
                                burst_len: int,
                                burst_size: int,
                                burst_type: int) -> Tuple[bool, str]:
        """
        Validate burst parameters according to AXI protocol rules.

        Args:
            addr: Starting address
            burst_len: Burst length (0=1 beat, 255=256 beats)
            burst_size: Burst size (0=1 byte, 1=2 bytes, 2=4 bytes, etc.)
            burst_type: Burst type (0=FIXED, 1=INCR, 2=WRAP)

        Returns:
            Tuple of (is_valid, error_message)
        """
        # Check address alignment
        bytes_per_beat = 1 << burst_size
        if addr % bytes_per_beat != 0:
            return False, f"Address 0x{addr:X} not aligned to size {burst_size} ({bytes_per_beat} bytes)"

        # Check burst length
        if burst_len < 0 or burst_len > 255:
            return False, f"Burst length {burst_len} out of range (0-255)"

        # Check burst size
        if burst_size < 0 or burst_size > 7:
            return False, f"Burst size {burst_size} out of range (0-7)"

        # Check burst type
        if burst_type not in [AXI4BaseSequence.BURST_FIXED, AXI4BaseSequence.BURST_INCR, AXI4BaseSequence.BURST_WRAP]:
            return False, f"Invalid burst type: {burst_type}"

        # Check WRAP burst requirements
        if burst_type == AXI4BaseSequence.BURST_WRAP:
            # Number of beats must be power of 2 for WRAP
            num_beats = burst_len + 1
            if not AXI4BaseSequence.is_power_of_two(num_beats):
                return False, f"WRAP burst length+1 must be 2, 4, 8, or 16, got {num_beats}"

            # WRAP burst shouldn't cross 4KB boundary
            total_bytes = num_beats * bytes_per_beat
            if total_bytes > 4096:
                return False, f"WRAP burst size exceeds 4KB boundary: {total_bytes} bytes"

        # Check 4KB boundary crossing for INCR
        if burst_type == AXI4BaseSequence.BURST_INCR:
            num_beats = burst_len + 1
            total_bytes = num_beats * bytes_per_beat
            start_page = addr // 4096
            end_addr = addr + total_bytes - 1
            end_page = end_addr // 4096

            if start_page != end_page:
                # Not an error, just a warning
                return True, f"INCR burst crosses 4KB boundary: 0x{addr:X} to 0x{end_addr:X} (allowed but inefficient)"

        return True, "Valid burst parameters"

    def get_stats(self) -> Dict[str, Any]:
        """
        Get sequence statistics.

        Returns:
            Dictionary of statistics
        """
        # Update memory usage estimate
        # This is a rough estimate based on object size
        self.stats['memory_usage'] = self._estimate_memory_usage()

        return self.stats

    def _estimate_memory_usage(self) -> int:
        """
        Estimate memory usage in bytes.
        This is a rough estimate and may not be accurate.

        Returns:
            Estimated memory usage in bytes
        """
        # Base size of the object
        base_size = 512  # Rough estimate for base object

        # Add size of last generated values
        values_size = len(self.last_generated_values) * 32  # Key + value + overhead per entry

        return base_size + values_size
