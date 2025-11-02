# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FieldConfig
# Purpose: FlexConfigGen - Helper class for creating FlexRandomizer configurations with wei
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
FlexConfigGen - Helper class for creating FlexRandomizer configurations with weighted bins.

This class simplifies the creation of FlexRandomizer constraint dictionaries by providing
a clean API for building weighted bin configurations and common shortcuts.
"""

from typing import Dict, List, Tuple, Union, Optional
from .flex_randomizer import FlexRandomizer


# Canned profiles for common timing patterns
DEFAULT_PROFILES = {
    # Always zero delay - for back-to-back transactions
    'backtoback': ([(0, 0)], [1]),

    # Fixed delays
    'fixed1': ([(1, 1)], [1]),                           # Always 1 cycle delay
    'fixed2': ([(2, 2)], [1]),                           # Always 2 cycle delay

    # Mostly zero with occasional small delays
    'mostly_zero': ([(0, 0), (1, 3)], [9, 1]),         # 90% zero, 10% small delay

    # Fast pattern - mostly zero, some small delays
    'fast': ([(0, 0), (1, 2)], [8, 1]),                # 89% zero, 11% tiny delay

    # Standard constrained pattern from project examples
    'constrained': ([(0, 0), (1, 8), (9, 20)], [5, 2, 1]), # Balanced distribution

    # Burst pattern - mostly zero with occasional long pauses
    'bursty': ([(0, 0), (15, 25)], [10, 1]),           # Fast bursts with pauses

    # Always has some delay
    'slow': ([(5, 10), (11, 20)], [3, 1]),             # Moderate to slow delays

    # Wide variation for stress testing
    'stress': ([(0, 2), (3, 8), (9, 20), (21, 50)], [4, 3, 2, 1]), # Full range stress

    # Additional meaningful profiles
    'moderate': ([(1, 3), (4, 8)], [3, 1]),                             # Never zero, small-medium delays
    'balanced': ([(0, 0), (1, 5), (6, 15)], [1, 1, 1]),                 # Equal probability ranges
    'heavy_pause': ([(0, 0), (20, 40)], [3, 1]),                        # Mostly fast with heavy pauses
    'gradual': ([(1, 2), (3, 5), (6, 10), (11, 20)], [8, 4, 2, 1]),     # Exponential falloff
    'jittery': ([(0, 1), (2, 4), (5, 8)], [2, 3, 2]),                   # Small random variations
    'pipeline': ([(2, 4), (8, 12)], [4, 1]),                            # Pipeline-friendly delays
    'throttled': ([(3, 7), (15, 30)], [7, 1]),                          # Controlled throughput
    'chaotic': ([(0, 5), (10, 15), (25, 35), (50, 80)], [3, 2, 2, 1]),  # Unpredictable timing
    'smooth': ([(2, 6), (7, 12)], [2, 1]),                              # Consistent moderate delays
    'efficient': ([(0, 0), (1, 1), (2, 3)], [6, 2, 1])                  # Optimized for throughput
}


class FieldConfig:
    """Configuration for a single field within a profile."""

    def __init__(self, field_name: str, profile_name: str):
        self.field_name = field_name
        self.profile_name = profile_name
        self.bins = []
        self.weights = []

    def add_bin(self, bin_range: Tuple[int, int], weight: Union[int, float]) -> 'FieldConfig':
        """
        Add a weighted bin to this field.

        Args:
            bin_range: Tuple of (min, max) values for the bin
            weight: Weight for this bin (relative to other bins)

        Returns:
            Self for method chaining

        Example:
            config.fast.psel.add_bin((0, 0), 8).add_bin((1, 5), 1)
            # Results in: 'psel': ([(0, 0), (1, 5)], [8, 1])
        """
        self.bins.append(bin_range)
        self.weights.append(weight)
        return self

    def clear(self) -> 'FieldConfig':
        """
        Clear all bins for this field.

        Returns:
            Self for method chaining
        """
        self.bins = []
        self.weights = []
        return self

    def fixed_value(self, value: int) -> 'FieldConfig':
        """
        Set field to always return a fixed value.

        Args:
            value: The fixed value to return

        Returns:
            Self for method chaining

        Example:
            config.fast.psel.fixed_value(0)
            # Results in: 'psel': ([(0, 0)], [1])
        """
        self.clear()
        self.add_bin((value, value), 1)
        return self

    def mostly_zero(self, zero_weight: Union[int, float] = 9,
                    fallback_range: Tuple[int, int] = (1, 5),
                    fallback_weight: Union[int, float] = 1) -> 'FieldConfig':
        """
        Create a pattern that's mostly zero with occasional other values.

        Args:
            zero_weight: Weight for the zero bin
            fallback_range: Range for non-zero values
            fallback_weight: Weight for the fallback range

        Returns:
            Self for method chaining

        Example:
            config.fast.psel.mostly_zero(zero_weight=15, fallback_range=(1, 8), fallback_weight=2)
            # Results in: 'psel': ([(0, 0), (1, 8)], [15, 2])
        """
        self.clear()
        self.add_bin((0, 0), zero_weight)
        self.add_bin(fallback_range, fallback_weight)
        return self

    def burst_pattern(self, fast_cycles: int = 0,
                        pause_range: Tuple[int, int] = (15, 25),
                        burst_ratio: Union[int, float] = 10) -> 'FieldConfig':
        """
        Create a burst pattern - mostly fast cycles with occasional pauses.

        Args:
            fast_cycles: Value for fast cycles (usually 0)
            pause_range: Range for pause delays
            burst_ratio: Ratio of fast to pause (higher = more fast cycles)

        Returns:
            Self for method chaining

        Example:
            config.bursty.psel.burst_pattern(fast_cycles=0, pause_range=(20, 30), burst_ratio=12)
            # Results in: 'psel': ([(0, 0), (20, 30)], [12, 1])
        """
        self.clear()
        self.add_bin((fast_cycles, fast_cycles), burst_ratio)
        self.add_bin(pause_range, 1)
        return self

    def uniform_range(self, min_val: int, max_val: int) -> 'FieldConfig':
        """
        Create a uniform distribution across a range.

        Args:
            min_val: Minimum value
            max_val: Maximum value

        Returns:
            Self for method chaining

        Example:
            config.slow.psel.uniform_range(5, 15)
            # Results in: 'psel': ([(5, 15)], [1])
        """
        self.clear()
        self.add_bin((min_val, max_val), 1)
        return self

    def weighted_ranges(self, range_weights: List[Tuple[Tuple[int, int], Union[int, float]]]) -> 'FieldConfig':
        """
        Set multiple weighted ranges at once.

        Args:
            range_weights: List of ((min, max), weight) tuples

        Returns:
            Self for method chaining

        Example:
            config.constrained.psel.weighted_ranges([
                ((0, 0), 5),
                ((1, 3), 3),
                ((10, 20), 1)
            ])
            # Results in: 'psel': ([(0, 0), (1, 3), (10, 20)], [5, 3, 1])
        """
        self.clear()
        for (min_val, max_val), weight in range_weights:
            self.add_bin((min_val, max_val), weight)
        return self

    def copy_from(self, other: 'FieldConfig') -> 'FieldConfig':
        """
        Copy configuration from another field.

        Args:
            other: Another FieldConfig to copy from

        Returns:
            Self for method chaining
        """
        self.clear()
        for bin_range, weight in zip(other.bins, other.weights):
            self.add_bin(bin_range, weight)
        return self

    def probability_split(self, prob_ranges: List[Tuple[Tuple[int, int], float]]) -> 'FieldConfig':
        """
        Set ranges based on probabilities (automatically converts to weights).

        Args:
            prob_ranges: List of ((min, max), probability) tuples
                        Probabilities should sum to 1.0

        Returns:
            Self for method chaining

        Example:
            config.fast.psel.probability_split([
                ((0, 0), 0.8),      # 80% chance
                ((1, 5), 0.2)       # 20% chance
            ])
            # Results in: 'psel': ([(0, 0), (1, 5)], [8, 2]) (scaled to integers)
        """
        self.clear()

        # Convert probabilities to integer weights (scale by 10 to avoid tiny decimals)
        scale_factor = 10
        for (min_val, max_val), prob in prob_ranges:
            weight = int(prob * scale_factor)
            if weight == 0:
                weight = 1  # Ensure no zero weights
            self.add_bin((min_val, max_val), weight)
        return self

    def to_constraint(self) -> Tuple[List[Tuple[int, int]], List[Union[int, float]]]:
        """
        Convert to the tuple format expected by FlexRandomizer.

        Returns:
            Tuple of (bins, weights) ready for FlexRandomizer
        """
        if not self.bins:
            raise ValueError(f"No bins defined for field '{self.field_name}' in profile '{self.profile_name}'")
        return (self.bins.copy(), self.weights.copy())


class ProfileConfig:
    """Configuration for all fields within a profile."""

    def __init__(self, profile_name: str, field_names: List[str], prefix: str = ""):
        self.profile_name = profile_name
        self.prefix = prefix
        self.fields = {}

        # Create FieldConfig objects for each field
        for field_name in field_names:
            full_field_name = f"{prefix}{field_name}" if prefix else field_name
            self.fields[field_name] = FieldConfig(full_field_name, profile_name)

    def __getattr__(self, field_name: str) -> FieldConfig:
        """Allow access to fields as attributes (e.g., config.fast.psel)."""
        if field_name in self.fields:
            return self.fields[field_name]
        raise AttributeError(f"Profile '{self.profile_name}' has no field '{field_name}'")


class FlexConfigGen:
    """
    Helper class for generating FlexRandomizer configurations with weighted bins.

    Simplifies creating constraint dictionaries by providing canned profiles,
    convenient shortcuts, and a clean API for building configurations.
    """

    def __init__(self, profiles: List[str], fields: List[str],
                    prefix: str = "", custom_profiles: Optional[Dict[str, Tuple]] = None):
        """
        Initialize the configuration generator.

        Args:
            profiles: List of profile names to create
            fields: List of field names (e.g., ['psel', 'penable'])
            prefix: Optional prefix for field names (default: empty)
            custom_profiles: Optional dict of custom profile definitions

        Example:
            config = FlexConfigGen(
                profiles=['backtoback', 'constrained', 'fast'],
                fields=['psel', 'penable'],
                custom_profiles={'my_pattern': ([(1, 1), (10, 15)], [8, 1])}
            )
        """
        self.profiles = {}
        self.field_names = fields
        self.prefix = prefix

        # Combine default and custom profiles
        all_profiles = DEFAULT_PROFILES.copy()
        if custom_profiles:
            all_profiles.update(custom_profiles)

        # Create ProfileConfig objects
        for profile_name in profiles:
            profile_config = ProfileConfig(profile_name, fields, prefix)

            # Initialize with canned profile if available
            if profile_name in all_profiles:
                bins, weights = all_profiles[profile_name]
                for field_name in fields:
                    field_config = profile_config.fields[field_name]
                    field_config.bins = bins.copy()
                    field_config.weights = weights.copy()

            self.profiles[profile_name] = profile_config

    def __getattr__(self, profile_name: str) -> ProfileConfig:
        """Allow access to profiles as attributes (e.g., config.fast)."""
        if profile_name in self.profiles:
            return self.profiles[profile_name]
        raise AttributeError(f"No profile named '{profile_name}'")

    def build(self, return_flexrandomizer: bool = True) -> Union[FlexRandomizer, Dict]:
        """
        Build the final configuration.

        Args:
            return_flexrandomizer: If True, return FlexRandomizer instance
                                    If False, return the constraint dictionary

        Returns:
            FlexRandomizer instance or constraint dictionary

        Example:
            # Get FlexRandomizer directly (default)
            randomizer = config.build()

            # Get dictionary for manual use
            constraint_dict = config.build(return_flexrandomizer=False)
        """
        result = {}

        for profile_name, profile_config in self.profiles.items():
            profile_dict = {}

            for field_name, field_config in profile_config.fields.items():
                full_field_name = f"{self.prefix}{field_name}" if self.prefix else field_name
                profile_dict[full_field_name] = field_config.to_constraint()

            result[profile_name] = profile_dict

        if return_flexrandomizer:
            # For FlexRandomizer, we need to flatten the structure
            # User will select which profile to use when creating FlexRandomizer
            # So we'll return a dict of FlexRandomizer instances
            flex_randomizers = {}
            for profile_name, profile_dict in result.items():
                flex_randomizers[profile_name] = FlexRandomizer(profile_dict)
            return flex_randomizers
        else:
            return result

    def get_available_profiles(self) -> List[str]:
        """Get list of available canned profiles."""
        return list(DEFAULT_PROFILES.keys())

    def get_profile_preview(self, profile_name: str) -> str:
        """Get a preview of what a canned profile looks like."""
        if profile_name in DEFAULT_PROFILES:
            bins, weights = DEFAULT_PROFILES[profile_name]
            return f"{profile_name}: (bins={bins}, weights={weights})"
        return f"Profile '{profile_name}' not found"


# Convenience function for quick creation
def quick_config(profiles: List[str], fields: List[str], **kwargs) -> FlexConfigGen:
    """
    Quick way to create a FlexConfigGen with common defaults.

    Args:
        profiles: List of profile names
        fields: List of field names
        **kwargs: Additional arguments for FlexConfigGen

    Returns:
        FlexConfigGen instance

    Example:
        config = quick_config(['fast', 'constrained'], ['psel', 'penable'])
        randomizer = config.build()['fast']  # Get the 'fast' profile randomizer
    """
    return FlexConfigGen(profiles, fields, **kwargs)
