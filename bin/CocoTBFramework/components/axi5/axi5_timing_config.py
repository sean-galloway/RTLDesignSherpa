# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axi5_timing_config
# Purpose: AXI5 Timing Configuration
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-16

"""
AXI5 Timing Configuration

Simple timing configuration for AXI5 components using existing FlexRandomizer infrastructure.
Provides common timing profiles for AXI5 testing with support for AXI5-specific features.
"""

from typing import Dict, Any, List
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer


def create_axi5_timing_from_profile(profile_name: str) -> Dict[str, Any]:
    """
    Create AXI5 timing configuration from a named profile.

    Args:
        profile_name: Timing profile name ('axi5_normal', 'axi5_fast', etc.)

    Returns:
        Dictionary with timing configuration
    """
    # Define timing profiles using existing FlexRandomizer patterns
    timing_profiles = {
        'axi5_normal': {
            'ar_valid_delay': ([(0, 3), (4, 8)], [0.7, 0.3]),
            'ar_ready_delay': ([(0, 2), (3, 6)], [0.8, 0.2]),
            'aw_valid_delay': ([(0, 3), (4, 8)], [0.7, 0.3]),
            'aw_ready_delay': ([(0, 2), (3, 6)], [0.8, 0.2]),
            'w_valid_delay': ([(0, 2), (3, 5)], [0.75, 0.25]),
            'w_ready_delay': ([(0, 2), (3, 5)], [0.8, 0.2]),
            'r_valid_delay': ([(1, 4), (5, 10)], [0.6, 0.4]),
            'r_ready_delay': ([(0, 3), (4, 7)], [0.7, 0.3]),
            'b_valid_delay': ([(1, 3), (4, 8)], [0.7, 0.3]),
            'b_ready_delay': ([(0, 2), (3, 5)], [0.8, 0.2]),
        },
        'axi5_fast': {
            'ar_valid_delay': ([(0, 1)], [1.0]),
            'ar_ready_delay': ([(0, 1)], [1.0]),
            'aw_valid_delay': ([(0, 1)], [1.0]),
            'aw_ready_delay': ([(0, 1)], [1.0]),
            'w_valid_delay': ([(0, 1)], [1.0]),
            'w_ready_delay': ([(0, 1)], [1.0]),
            'r_valid_delay': ([(0, 2)], [1.0]),
            'r_ready_delay': ([(0, 1)], [1.0]),
            'b_valid_delay': ([(0, 2)], [1.0]),
            'b_ready_delay': ([(0, 1)], [1.0]),
        },
        'axi5_slow': {
            'ar_valid_delay': ([(5, 15)], [1.0]),
            'ar_ready_delay': ([(3, 12)], [1.0]),
            'aw_valid_delay': ([(5, 15)], [1.0]),
            'aw_ready_delay': ([(3, 12)], [1.0]),
            'w_valid_delay': ([(4, 12)], [1.0]),
            'w_ready_delay': ([(3, 10)], [1.0]),
            'r_valid_delay': ([(8, 20)], [1.0]),
            'r_ready_delay': ([(5, 15)], [1.0]),
            'b_valid_delay': ([(6, 18)], [1.0]),
            'b_ready_delay': ([(4, 12)], [1.0]),
        },
        'axi5_backtoback': {
            'ar_valid_delay': ([(0, 0)], [1.0]),
            'ar_ready_delay': ([(0, 0)], [1.0]),
            'aw_valid_delay': ([(0, 0)], [1.0]),
            'aw_ready_delay': ([(0, 0)], [1.0]),
            'w_valid_delay': ([(0, 0)], [1.0]),
            'w_ready_delay': ([(0, 0)], [1.0]),
            'r_valid_delay': ([(0, 0)], [1.0]),
            'r_ready_delay': ([(0, 0)], [1.0]),
            'b_valid_delay': ([(0, 0)], [1.0]),
            'b_ready_delay': ([(0, 0)], [1.0]),
        },
        'axi5_stress': {
            'ar_valid_delay': ([(0, 0), (10, 25)], [0.3, 0.7]),
            'ar_ready_delay': ([(0, 0), (15, 30)], [0.4, 0.6]),
            'aw_valid_delay': ([(0, 0), (10, 25)], [0.3, 0.7]),
            'aw_ready_delay': ([(0, 0), (15, 30)], [0.4, 0.6]),
            'w_valid_delay': ([(0, 0), (8, 20)], [0.35, 0.65]),
            'w_ready_delay': ([(0, 0), (10, 25)], [0.4, 0.6]),
            'r_valid_delay': ([(0, 0), (12, 28)], [0.3, 0.7]),
            'r_ready_delay': ([(0, 0), (8, 20)], [0.5, 0.5]),
            'b_valid_delay': ([(0, 0), (10, 24)], [0.35, 0.65]),
            'b_ready_delay': ([(0, 0), (6, 18)], [0.5, 0.5]),
        },
        'axi5_atomic': {
            # Atomic operations may need longer response times
            'ar_valid_delay': ([(0, 2)], [1.0]),
            'ar_ready_delay': ([(0, 2)], [1.0]),
            'aw_valid_delay': ([(0, 2)], [1.0]),
            'aw_ready_delay': ([(0, 2)], [1.0]),
            'w_valid_delay': ([(0, 1)], [1.0]),
            'w_ready_delay': ([(0, 1)], [1.0]),
            'r_valid_delay': ([(2, 8)], [1.0]),  # Atomic reads may take longer
            'r_ready_delay': ([(0, 1)], [1.0]),
            'b_valid_delay': ([(2, 8)], [1.0]),  # Atomic responses may take longer
            'b_ready_delay': ([(0, 1)], [1.0]),
        },
        'axi5_mte': {
            # Memory Tagging operations similar to normal but slightly slower
            'ar_valid_delay': ([(0, 3), (4, 8)], [0.6, 0.4]),
            'ar_ready_delay': ([(0, 2), (3, 6)], [0.7, 0.3]),
            'aw_valid_delay': ([(0, 3), (4, 8)], [0.6, 0.4]),
            'aw_ready_delay': ([(0, 2), (3, 6)], [0.7, 0.3]),
            'w_valid_delay': ([(0, 3), (4, 6)], [0.65, 0.35]),
            'w_ready_delay': ([(0, 2), (3, 5)], [0.75, 0.25]),
            'r_valid_delay': ([(1, 5), (6, 12)], [0.5, 0.5]),  # Tag check overhead
            'r_ready_delay': ([(0, 3), (4, 7)], [0.7, 0.3]),
            'b_valid_delay': ([(1, 4), (5, 10)], [0.6, 0.4]),  # Tag update overhead
            'b_ready_delay': ([(0, 2), (3, 5)], [0.8, 0.2]),
        },
        'axi5_secure': {
            # Security-focused timing with moderate delays
            'ar_valid_delay': ([(1, 4), (5, 10)], [0.6, 0.4]),
            'ar_ready_delay': ([(0, 3), (4, 8)], [0.7, 0.3]),
            'aw_valid_delay': ([(1, 4), (5, 10)], [0.6, 0.4]),
            'aw_ready_delay': ([(0, 3), (4, 8)], [0.7, 0.3]),
            'w_valid_delay': ([(1, 3), (4, 7)], [0.65, 0.35]),
            'w_ready_delay': ([(0, 3), (4, 6)], [0.75, 0.25]),
            'r_valid_delay': ([(2, 6), (7, 14)], [0.5, 0.5]),
            'r_ready_delay': ([(0, 3), (4, 8)], [0.7, 0.3]),
            'b_valid_delay': ([(2, 5), (6, 12)], [0.55, 0.45]),
            'b_ready_delay': ([(0, 2), (3, 6)], [0.75, 0.25]),
        },
        'axi5_chunked': {
            # Chunked transfers need special timing
            'ar_valid_delay': ([(0, 2), (3, 6)], [0.7, 0.3]),
            'ar_ready_delay': ([(0, 2), (3, 5)], [0.8, 0.2]),
            'aw_valid_delay': ([(0, 2), (3, 6)], [0.7, 0.3]),
            'aw_ready_delay': ([(0, 2), (3, 5)], [0.8, 0.2]),
            'w_valid_delay': ([(0, 2), (3, 5)], [0.75, 0.25]),
            'w_ready_delay': ([(0, 2), (3, 4)], [0.85, 0.15]),
            'r_valid_delay': ([(0, 3), (4, 8)], [0.6, 0.4]),  # Chunk assembly overhead
            'r_ready_delay': ([(0, 2), (3, 5)], [0.8, 0.2]),
            'b_valid_delay': ([(1, 3), (4, 7)], [0.7, 0.3]),
            'b_ready_delay': ([(0, 2), (3, 5)], [0.8, 0.2]),
        },
    }

    # Get profile or default to normal
    constraints = timing_profiles.get(profile_name, timing_profiles['axi5_normal'])

    # Create FlexRandomizer with the constraints
    randomizer = FlexRandomizer(constraints)

    return {
        'profile_name': profile_name,
        'randomizer': randomizer,
        'constraints': constraints
    }


def get_axi5_timing_profiles() -> List[str]:
    """Get list of available AXI5 timing profiles."""
    return [
        'axi5_normal',
        'axi5_fast',
        'axi5_slow',
        'axi5_backtoback',
        'axi5_stress',
        'axi5_atomic',
        'axi5_mte',
        'axi5_secure',
        'axi5_chunked',
    ]


def create_axi5_randomizer_configs() -> Dict[str, Any]:
    """
    Create randomizer configurations for different test profiles.

    Returns:
        Dictionary of randomizer configurations
    """
    return {
        'normal': create_axi5_timing_from_profile('axi5_normal'),
        'fast': create_axi5_timing_from_profile('axi5_fast'),
        'slow': create_axi5_timing_from_profile('axi5_slow'),
        'backtoback': create_axi5_timing_from_profile('axi5_backtoback'),
        'stress': create_axi5_timing_from_profile('axi5_stress'),
        'atomic': create_axi5_timing_from_profile('axi5_atomic'),
        'mte': create_axi5_timing_from_profile('axi5_mte'),
        'secure': create_axi5_timing_from_profile('axi5_secure'),
        'chunked': create_axi5_timing_from_profile('axi5_chunked'),
    }


def get_timing_for_axi5_feature(feature: str) -> Dict[str, Any]:
    """
    Get recommended timing profile for a specific AXI5 feature.

    Args:
        feature: AXI5 feature name ('atomic', 'mte', 'secure', 'chunked')

    Returns:
        Timing configuration dictionary
    """
    feature_mapping = {
        'atomic': 'axi5_atomic',
        'atop': 'axi5_atomic',
        'mte': 'axi5_mte',
        'tag': 'axi5_mte',
        'secure': 'axi5_secure',
        'security': 'axi5_secure',
        'nsaid': 'axi5_secure',
        'mpam': 'axi5_secure',
        'mecid': 'axi5_secure',
        'chunk': 'axi5_chunked',
        'chunked': 'axi5_chunked',
    }

    profile_name = feature_mapping.get(feature.lower(), 'axi5_normal')
    return create_axi5_timing_from_profile(profile_name)
