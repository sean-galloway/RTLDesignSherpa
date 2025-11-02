# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axi4_timing_config
# Purpose: AXI4 Timing Configuration
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Timing Configuration

Simple timing configuration for AXI4 components using existing FlexRandomizer infrastructure.
Provides common timing profiles for AXI4 testing.
"""

from typing import Dict, Any
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer


def create_axi4_timing_from_profile(profile_name: str) -> Dict[str, Any]:
    """
    Create AXI4 timing configuration from a named profile.
    
    Args:
        profile_name: Timing profile name ('axi4_normal', 'axi4_fast', etc.)
        
    Returns:
        Dictionary with timing configuration
    """
    # Define timing profiles using existing FlexRandomizer patterns
    timing_profiles = {
        'axi4_normal': {
            'ar_valid_delay': ([(0, 3), (4, 8)], [0.7, 0.3]),
            'ar_ready_delay': ([(0, 2), (3, 6)], [0.8, 0.2]),
            'r_valid_delay': ([(1, 4), (5, 10)], [0.6, 0.4]),
            'r_ready_delay': ([(0, 3), (4, 7)], [0.7, 0.3]),
        },
        'axi4_fast': {
            'ar_valid_delay': ([(0, 1)], [1.0]),
            'ar_ready_delay': ([(0, 1)], [1.0]),
            'r_valid_delay': ([(0, 2)], [1.0]),
            'r_ready_delay': ([(0, 1)], [1.0]),
        },
        'axi4_slow': {
            'ar_valid_delay': ([(5, 15)], [1.0]),
            'ar_ready_delay': ([(3, 12)], [1.0]),
            'r_valid_delay': ([(8, 20)], [1.0]),
            'r_ready_delay': ([(5, 15)], [1.0]),
        },
        'axi4_backtoback': {
            'ar_valid_delay': ([(0, 0)], [1.0]),
            'ar_ready_delay': ([(0, 0)], [1.0]),
            'r_valid_delay': ([(0, 0)], [1.0]),
            'r_ready_delay': ([(0, 0)], [1.0]),
        },
        'axi4_stress': {
            'ar_valid_delay': ([(0, 0), (10, 25)], [0.3, 0.7]),
            'ar_ready_delay': ([(0, 0), (15, 30)], [0.4, 0.6]),
            'r_valid_delay': ([(0, 0), (12, 28)], [0.3, 0.7]),
            'r_ready_delay': ([(0, 0), (8, 20)], [0.5, 0.5]),
        }
    }
    
    # Get profile or default to normal
    constraints = timing_profiles.get(profile_name, timing_profiles['axi4_normal'])
    
    # Create FlexRandomizer with the constraints
    randomizer = FlexRandomizer(constraints)
    
    return {
        'profile_name': profile_name,
        'randomizer': randomizer,
        'constraints': constraints
    }


def get_axi4_timing_profiles():
    """Get list of available AXI4 timing profiles."""
    return ['axi4_normal', 'axi4_fast', 'axi4_slow', 'axi4_backtoback', 'axi4_stress']


def create_axi4_randomizer_configs():
    """
    Create randomizer configurations for different test profiles.
    
    Returns:
        Dictionary of randomizer configurations
    """
    return {
        'normal': create_axi4_timing_from_profile('axi4_normal'),
        'fast': create_axi4_timing_from_profile('axi4_fast'),
        'slow': create_axi4_timing_from_profile('axi4_slow'),
        'backtoback': create_axi4_timing_from_profile('axi4_backtoback'),
        'stress': create_axi4_timing_from_profile('axi4_stress')
    }
