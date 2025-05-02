"""
AXI4 Randomization Configuration

This module provides AXI4-specific randomization configuration and utilities.
"""

from typing import Dict, List, Any, Optional, Union, Callable, Tuple
from ..randomization_config import RandomizationConfig, FieldRandomizationConfig, RandomizationMode

from ..flex_randomizer import FlexRandomizer


class AXI4RandomizationConfig(RandomizationConfig):
    """
    AXI4-specific randomization configuration.

    This class extends the base RandomizationConfig with predefined
    configurations and utilities for AXI4 protocol signals.
    """

    # AXI4 burst types
    BURST_FIXED = 0
    BURST_INCR = 1
    BURST_WRAP = 2

    # AXI4 response types
    RESP_OKAY = 0
    RESP_EXOKAY = 1
    RESP_SLVERR = 2
    RESP_DECERR = 3

    def __init__(self, seed: Optional[int] = None):
        """
        Initialize AXI4-specific randomization configuration.

        Args:
            seed: Random seed for reproducibility
        """
        super().__init__(protocol_name="AXI4", seed=seed)

        # Create utility randomizers
        self._utility_randomizer = FlexRandomizer({})

        # Define common field groups
        self._setup_field_groups()

        # Apply default configurations
        self._apply_default_configs()

    def _setup_field_groups(self):
        """Setup predefined field groups for AXI4."""
        # Address channel fields
        self.add_to_group('addr_fields', 'awaddr')
        self.add_to_group('addr_fields', 'araddr')

        # ID fields
        self.add_to_group('id_fields', 'awid')
        self.add_to_group('id_fields', 'arid')
        self.add_to_group('id_fields', 'bid')
        self.add_to_group('id_fields', 'rid')

        # Burst control fields
        self.add_to_group('burst_type_fields', 'awburst')
        self.add_to_group('burst_type_fields', 'arburst')

        self.add_to_group('burst_len_fields', 'awlen')
        self.add_to_group('burst_len_fields', 'arlen')

        self.add_to_group('burst_size_fields', 'awsize')
        self.add_to_group('burst_size_fields', 'arsize')

        # Lock fields
        self.add_to_group('lock_fields', 'awlock')
        self.add_to_group('lock_fields', 'arlock')

        # Protection fields
        self.add_to_group('prot_fields', 'awprot')
        self.add_to_group('prot_fields', 'arprot')

        # QoS fields
        self.add_to_group('qos_fields', 'awqos')
        self.add_to_group('qos_fields', 'arqos')

        # User fields
        self.add_to_group('user_fields', 'awuser')
        self.add_to_group('user_fields', 'aruser')
        self.add_to_group('user_fields', 'wuser')
        self.add_to_group('user_fields', 'buser')
        self.add_to_group('user_fields', 'ruser')

        # Response fields
        self.add_to_group('resp_fields', 'bresp')
        self.add_to_group('resp_fields', 'rresp')

        # Data fields
        self.add_to_group('data_fields', 'wdata')
        self.add_to_group('data_fields', 'rdata')

    def _apply_default_configs(self):
        """Apply default configurations for AXI4 fields."""
        # Configure ID fields (typically 4-8 bits)
        self.configure_group('id_fields',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": [(0, 15)],  # Default to 4-bit IDs
                                "weights": [1.0]
                            })

        # Configure address fields
        self.configure_group('addr_fields',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": [(0, 0xFFFFFFFF)],  # 32-bit address space
                                "weights": [1.0]
                            })

        # Configure burst types with weights
        # Favor INCR bursts as they're most common
        self.configure_group('burst_type_fields',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": [(self.BURST_FIXED, self.BURST_FIXED),
                                        (self.BURST_INCR, self.BURST_INCR),
                                        (self.BURST_WRAP, self.BURST_WRAP)],
                                "weights": [0.1, 0.8, 0.1]  # 10% FIXED, 80% INCR, 10% WRAP
                            })

        # Configure burst lengths
        # Favor shorter bursts but allow longer ones
        self.configure_group('burst_len_fields',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": [(0, 0),     # Single beat (most common)
                                        (1, 3),     # 2-4 beats
                                        (4, 15),    # 5-16 beats
                                        (16, 255)], # 17-256 beats (less common)
                                "weights": [0.4, 0.3, 0.2, 0.1]
                            })

        # Configure burst sizes
        # Favor data width aligned transfers
        self.configure_group('burst_size_fields',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": [(0, 0),  # 1 byte
                                        (1, 1),  # 2 bytes
                                        (2, 2),  # 4 bytes (word)
                                        (3, 3)], # 8 bytes (double word)
                                "weights": [0.1, 0.1, 0.6, 0.2]
                            })

        # Configure lock fields (mostly non-exclusive)
        self.configure_group('lock_fields',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": [(0, 0), (1, 1)],  # 0=normal, 1=exclusive
                                "weights": [0.9, 0.1]      # 90% normal, 10% exclusive
                            })

        # Configure protection fields
        # Generate all 8 combinations of protection bits
        self.configure_group('prot_fields',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": [(0, 7)],  # All 8 combinations (0-7)
                                "weights": [1.0]
                            })

        # Configure QoS fields
        # Favor lower QoS values
        self.configure_group('qos_fields',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": [(0, 0),   # No QoS (most common)
                                        (1, 7),   # Medium priority
                                        (8, 15)], # High priority (less common)
                                "weights": [0.6, 0.3, 0.1]
                            })

        # Configure response fields
        # Mostly OKAY, sometimes errors
        self.configure_group('resp_fields',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": [(self.RESP_OKAY, self.RESP_OKAY),     # OKAY
                                        (self.RESP_EXOKAY, self.RESP_EXOKAY), # EXOKAY
                                        (self.RESP_SLVERR, self.RESP_SLVERR), # SLVERR
                                        (self.RESP_DECERR, self.RESP_DECERR)], # DECERR
                                "weights": [0.85, 0.05, 0.05, 0.05]
                            })

        # Configure data fields (no specific pattern)
        self.configure_group('data_fields',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": [(0, 0xFFFFFFFF)],  # Full 32-bit range
                                "weights": [1.0]
                            })

    def get_address_aligned_to_size(self, addr: int, size: int) -> int:
        """
        Get an address properly aligned to the specified size.

        Args:
            addr: Original address
            size: Burst size (0=1 byte, 1=2 bytes, 2=4 bytes, etc.)

        Returns:
            Aligned address
        """
        # Calculate alignment mask
        alignment = 1 << size
        mask = alignment - 1

        # Align address (clear low bits)
        return addr & ~mask

    def get_legal_burst_length(self, burst_type: int, addr: int, size: int) -> int:
        """
        Get a legal burst length for the specified parameters.

        Args:
            burst_type: Burst type (0=FIXED, 1=INCR, 2=WRAP)
            addr: Address
            size: Burst size

        Returns:
            Legal burst length
        """
        if burst_type == self.BURST_WRAP:
            # WRAP bursts must have len+1 as power of 2
            # Use FlexRandomizer to choose from 2, 4, 8, or 16
            wrap_constraints = {
                "wrap_len": {
                    "bins": [(1, 1), (3, 3), (7, 7), (15, 15)],  # 2, 4, 8, 16 beats
                    "weights": [0.25, 0.25, 0.25, 0.25]  # Equal weights
                }
            }
            return self._get_legal_burst_length_helper(
                wrap_constraints, "wrap_len", 1
            )
        # For FIXED and INCR, any length is legal
        # but check 4KB boundary for INCR
        if burst_type == self.BURST_INCR:
            # Calculate bytes per beat
            bytes_per_beat = 1 << size

            # Calculate how many beats until 4KB boundary
            addr_4k_offset = addr & 0xFFF
            beats_to_boundary = (0x1000 - addr_4k_offset) // bytes_per_beat

            # Limit to boundary or 256 beats, whichever is smaller
            max_beats = min(256, beats_to_boundary)

            # Choose a reasonable length using FlexRandomizer
            if max_beats <= 1:
                return 0  # Single beat
            elif max_beats <= 16:
                # Use a randomizer for the range
                len_constraints = {
                    "burst_len": {
                        "bins": [(0, max_beats - 1)],
                        "weights": [1.0]
                    }
                }
                return self._get_legal_burst_length_helper(
                    len_constraints, "burst_len", 0
                )
            else:
                # Favor shorter bursts using multiple bins with different weights
                len_constraints = {
                    "burst_len": {
                        "bins": [(0, 3), (4, 15), (16, min(255, max_beats - 1))],
                        "weights": [0.6, 0.3, 0.1]  # 60% short, 30% medium, 10% long
                    }
                }
                return self._get_legal_burst_length_helper(
                    len_constraints, "burst_len", 0
                )
        # For FIXED, any length up to 255 is fine
        # Favor shorter bursts for simplicity
        fixed_constraints = {
            "burst_len": {
                "bins": [(0, 15)],
                "weights": [1.0]
            }
        }
        return self._get_legal_burst_length_helper(
            fixed_constraints, "burst_len", 0
        )

    def _get_legal_burst_length_helper(self, arg0, arg1, arg2):
        wrap_randomizer = FlexRandomizer(arg0)
        result = wrap_randomizer.next()
        return result.get(arg1, arg2)

    def configure_for_data_width(self, data_width: int = 32) -> 'AXI4RandomizationConfig':
        """
        Configure randomization for a specific data width.

        Args:
            data_width: Data width in bits

        Returns:
            Self for method chaining
        """
        # Update data field constraints
        data_mask = (1 << data_width) - 1

        self.configure_group('data_fields',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": [(0, data_mask)],
                                "weights": [1.0]
                            })

        # Update strobe width based on data width
        strb_width = data_width // 8
        strb_mask = (1 << strb_width) - 1

        # Configure write strobe
        self.configure_field('wstrb',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": [(0, strb_mask)],
                                "weights": [1.0]
                            })

        # Update burst size to match data width
        max_size_log2 = 0
        while (1 << max_size_log2) < (data_width // 8):
            max_size_log2 += 1

        # Configure burst sizes up to data width
        bins = [(i, i) for i in range(max_size_log2 + 1)]

        # Calculate weights using FlexRandomizer for consistency
        # Higher weight for max size, equal weights for smaller sizes
        weight_per_small_size = 0.1
        total_small_weight = weight_per_small_size * max_size_log2
        max_size_weight = 0.1 + 0.9 * (1.0 - total_small_weight)

        weights = [weight_per_small_size] * max_size_log2
        weights.append(max_size_weight)

        self.configure_group('burst_size_fields',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": bins,
                                "weights": weights
                            })

        return self

    def set_exclusive_access_mode(self, probability: float = 0.1) -> 'AXI4RandomizationConfig':
        """
        Configure the probability of exclusive access transactions.

        Args:
            probability: Probability of exclusive access (0.0-1.0)

        Returns:
            Self for method chaining
        """
        # Validate probability
        if probability < 0.0 or probability > 1.0:
            raise ValueError("Probability must be between 0.0 and 1.0")

        # Update lock field configuration
        self.configure_group('lock_fields',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": [(0, 0), (1, 1)],
                                "weights": [1.0 - probability, probability]
                            })

        return self

    def set_error_injection_rate(self, error_rate: float = 0.05) -> 'AXI4RandomizationConfig':
        """
        Configure the rate of error responses.

        Args:
            error_rate: Rate of error responses (0.0-1.0)

        Returns:
            Self for method chaining
        """
        # Validate error rate
        if error_rate < 0.0 or error_rate > 1.0:
            raise ValueError("Error rate must be between 0.0 and 1.0")

        # Calculate individual probabilities
        okay_prob = 1.0 - error_rate
        # Split errors between SLVERR and DECERR, with small chance of EXOKAY
        exokay_prob = min(0.05, error_rate * 0.2)
        remaining = error_rate - exokay_prob
        slverr_prob = remaining * 0.6
        decerr_prob = remaining * 0.4

        # Update response field configuration
        self.configure_group('resp_fields',
                            mode=RandomizationMode.CONSTRAINED,
                            constraints={
                                "bins": [(self.RESP_OKAY, self.RESP_OKAY),
                                        (self.RESP_EXOKAY, self.RESP_EXOKAY),
                                        (self.RESP_SLVERR, self.RESP_SLVERR),
                                        (self.RESP_DECERR, self.RESP_DECERR)],
                                "weights": [okay_prob, exokay_prob, slverr_prob, decerr_prob]
                            })

        return self

    def configure_field(self, field_name, config=None, **kwargs):
        """
        Configure randomization for a specific field.
        
        This method provides backward compatibility by accepting either:
        1. A FieldRandomizationConfig object as the second parameter
        2. Individual parameters as keyword arguments
        
        Args:
            field_name: Name of the field to configure
            config: FieldRandomizationConfig object (optional)
            **kwargs: Individual configuration parameters
            
        Returns:
            Self for method chaining
        """
        # Handle both calling patterns
        if config is not None:
            # Called with a FieldRandomizationConfig object
            return super().configure_field(field_name, config)
        
        # Called with individual parameters
        # Convert them to a FieldRandomizationConfig
        from ..randomization_config import FieldRandomizationConfig, RandomizationMode
        
        # Extract parameters
        mode = kwargs.get('mode', RandomizationMode.CONSTRAINED)
        constraints = kwargs.get('constraints')
        sequence = kwargs.get('sequence')
        custom_generator = kwargs.get('custom_generator')
        dependencies = kwargs.get('dependencies', [])
        
        # Create the config object
        field_config = FieldRandomizationConfig(
            mode=mode,
            constraints=constraints,
            sequence=sequence,
            custom_generator=custom_generator,
            dependencies=dependencies
        )
        
        # Use parent method with the config object
        return super().configure_field(field_name, field_config)
