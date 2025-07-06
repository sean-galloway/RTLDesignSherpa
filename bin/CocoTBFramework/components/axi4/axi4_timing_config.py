"""
AXI4 Timing Configuration - Clean Implementation

This module provides AXI4-specific timing configuration using FlexRandomizer
and FlexConfigGen for efficient ready/valid handshake timing patterns.

FlexConfigGen is always available - no fallback logic needed.
"""

from typing import Dict, List, Optional, Union, Any
from ..shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.flex_config_gen import FlexConfigGen


class AXI4TimingConfig:
    """
    AXI4-specific timing configuration using FlexRandomizer for realistic timing patterns.

    This class provides pre-configured timing profiles optimized for AXI4 verification,
    supporting both master and slave side timing control.
    """

    # AXI4-specific timing profiles
    AXI4_TIMING_PROFILES = {
        # Standard AXI4 patterns
        'axi4_fast': ([(0, 0), (1, 1)], [9, 1]),                    # 90% back-to-back, 10% single cycle
        'axi4_normal': ([(0, 0), (1, 3), (4, 8)], [6, 3, 1]),      # Balanced for typical usage
        'axi4_bursty': ([(0, 0), (8, 15)], [8, 1]),                # Fast bursts with pauses
        'axi4_throttled': ([(2, 5), (10, 20)], [7, 1]),            # Controlled throughput
        'axi4_stress': ([(0, 1), (2, 10), (15, 30)], [3, 4, 1]),   # Stress testing

        # Channel-specific optimized patterns
        'aw_optimized': ([(0, 0), (1, 2), (5, 10)], [7, 2, 1]),    # Address channel optimized
        'w_optimized': ([(0, 0), (1, 1), (3, 5)], [8, 1, 1]),      # Data channel optimized
        'b_optimized': ([(0, 1), (2, 4)], [8, 2]),                 # Response channel optimized
        'ar_optimized': ([(0, 0), (1, 3), (6, 12)], [6, 3, 1]),    # Read address optimized
        'r_optimized': ([(0, 0), (1, 2), (4, 8)], [7, 2, 1]),      # Read data optimized

        # Performance-specific patterns
        'high_throughput': ([(0, 0), (1, 1)], [9, 1]),             # Maximum throughput
        'low_latency': ([(0, 0)], [1]),                             # Zero latency
        'balanced': ([(0, 0), (1, 2), (3, 6)], [7, 2, 1]),         # Balanced performance
        
        # Compliance patterns
        'compliance': ([(0, 0), (1, 1), (2, 2)], [6, 3, 1]),       # Predictable for compliance
        'deterministic': ([(1, 1)], [1]),                          # Fixed single cycle delay
    }

    def __init__(self, master_profile: str = 'axi4_normal', slave_profile: str = 'axi4_normal',
                 custom_profiles: Optional[Dict[str, tuple]] = None):
        """
        Initialize AXI4 timing configuration.

        Args:
            master_profile: Default profile for master-side timing
            slave_profile: Default profile for slave-side timing
            custom_profiles: Optional custom timing profiles
        """
        self.master_profile = master_profile
        self.slave_profile = slave_profile

        # Combine default and custom profiles
        self.all_profiles = self.AXI4_TIMING_PROFILES.copy()
        if custom_profiles:
            self.all_profiles.update(custom_profiles)

        # Validate profiles exist
        if master_profile not in self.all_profiles:
            raise ValueError(f"Master profile '{master_profile}' not found. Available: {list(self.all_profiles.keys())}")
        if slave_profile not in self.all_profiles:
            raise ValueError(f"Slave profile '{slave_profile}' not found. Available: {list(self.all_profiles.keys())}")

        # Channel-specific randomizers cache
        self._randomizer_cache = {}

    def get_master_randomizers(self, channels: Optional[List[str]] = None) -> Dict[str, FlexRandomizer]:
        """
        Get FlexRandomizer instances for master-side timing.

        Args:
            channels: List of channels to create randomizers for (default: ['AW', 'W', 'AR'])

        Returns:
            Dictionary of FlexRandomizer instances by profile
        """
        if channels is None:
            channels = ['AW', 'W', 'AR']

        # Generate field names for master side (valid signals)
        fields = [f"{ch.lower()}_valid_delay" for ch in channels]

        # Create FlexConfigGen
        config_gen = FlexConfigGen(
            profiles=[self.master_profile, 'axi4_fast', 'axi4_bursty', 'axi4_stress'],
            fields=fields,
            custom_profiles=self.all_profiles
        )
        
        return config_gen.build()

    def get_slave_randomizers(self, channels: Optional[List[str]] = None) -> Dict[str, FlexRandomizer]:
        """
        Get FlexRandomizer instances for slave-side timing.

        Args:
            channels: List of channels to create randomizers for (default: all AXI4 channels)

        Returns:
            Dictionary of FlexRandomizer instances by profile
        """
        if channels is None:
            channels = ['AW', 'W', 'B', 'AR', 'R']

        # Generate field names for slave side (ready signals)
        fields = [f"{ch.lower()}_ready_delay" for ch in channels]

        # Create FlexConfigGen
        config_gen = FlexConfigGen(
            profiles=[self.slave_profile, 'axi4_normal', 'axi4_throttled', 'axi4_stress'],
            fields=fields,
            custom_profiles=self.all_profiles
        )
        
        return config_gen.build()

    def get_response_randomizers(self, channels: Optional[List[str]] = None) -> Dict[str, FlexRandomizer]:
        """
        Get FlexRandomizer instances for response timing.

        Args:
            channels: List of response channels (default: ['B', 'R'])

        Returns:
            Dictionary of FlexRandomizer instances by profile
        """
        if channels is None:
            channels = ['B', 'R']

        # Generate field names for response channels (valid signals)
        fields = [f"{ch.lower()}_valid_delay" for ch in channels]

        # Create FlexConfigGen
        config_gen = FlexConfigGen(
            profiles=[self.slave_profile, 'axi4_normal', 'b_optimized', 'r_optimized'],
            fields=fields,
            custom_profiles=self.all_profiles
        )
        
        return config_gen.build()

    def get_channel_randomizer(self, channel: str, side: str = 'master', profile: str = None) -> FlexRandomizer:
        """
        Get a FlexRandomizer for a specific channel and side.

        Args:
            channel: AXI4 channel ('AW', 'W', 'B', 'AR', 'R')
            side: 'master', 'slave', or 'response'
            profile: Profile to use (default: master_profile or slave_profile)

        Returns:
            FlexRandomizer instance for the specific channel
        """
        # Determine profile
        if profile is None:
            profile = self.master_profile if side == 'master' else self.slave_profile

        # Generate field name
        ch = channel.lower()
        if side == 'master':
            field_name = f"{ch}_valid_delay"
        elif side == 'response':
            field_name = f"{ch}_valid_delay"
        else:  # slave
            field_name = f"{ch}_ready_delay"

        # Get constraints for the profile
        if profile not in self.all_profiles:
            raise ValueError(f"Profile '{profile}' not found")

        constraints = self.all_profiles[profile]
        
        # Create and return FlexRandomizer
        return FlexRandomizer({field_name: constraints})

    def create_channel_specific_config(self, channels: List[str]) -> 'AXI4TimingConfig':
        """
        Create a timing config optimized for specific channels.

        Args:
            channels: List of AXI4 channels to optimize for

        Returns:
            New AXI4TimingConfig instance optimized for the channels
        """
        # Select optimized profiles based on channels
        master_profile = self.master_profile
        slave_profile = self.slave_profile

        if set(channels) == {'AW', 'W', 'B'}:
            # Write-only configuration
            master_profile = 'aw_optimized'
            slave_profile = 'axi4_fast'
        elif set(channels) == {'AR', 'R'}:
            # Read-only configuration
            master_profile = 'ar_optimized'
            slave_profile = 'axi4_normal'
        elif len(channels) == 1:
            # Single channel optimization
            channel_profiles = {
                'AW': 'aw_optimized',
                'W': 'w_optimized',
                'B': 'b_optimized',
                'AR': 'ar_optimized',
                'R': 'r_optimized'
            }
            profile = channel_profiles.get(channels[0], self.master_profile)
            master_profile = slave_profile = profile

        return AXI4TimingConfig(master_profile, slave_profile, self.all_profiles)

    def get_profile_info(self) -> Dict[str, Any]:
        """
        Get information about configured profiles.

        Returns:
            Dictionary with profile information
        """
        return {
            'master_profile': self.master_profile,
            'slave_profile': self.slave_profile,
            'available_profiles': list(self.all_profiles.keys()),
            'master_fields': ['aw_valid_delay', 'w_valid_delay', 'ar_valid_delay'],
            'slave_fields': ['aw_ready_delay', 'w_ready_delay', 'b_ready_delay', 'ar_ready_delay', 'r_ready_delay'],
            'response_fields': ['b_valid_delay', 'r_valid_delay']
        }

    # Class methods for creating specific configurations

    @classmethod
    def create_performance_config(cls, performance_mode: str = 'normal', 
                                component_type: str = 'master') -> 'AXI4TimingConfig':
        """
        Create a timing configuration for specific performance requirements.

        Args:
            performance_mode: 'high_throughput', 'low_latency', 'balanced', 'normal', 'stress'
            component_type: 'master', 'slave', or 'both'

        Returns:
            AXI4TimingConfig instance optimized for the performance mode
        """
        # Map performance modes to timing profiles
        performance_map = {
            'high_throughput': 'high_throughput',
            'low_latency': 'low_latency',
            'balanced': 'balanced',
            'normal': 'axi4_normal',
            'stress': 'axi4_stress',
            'fast': 'axi4_fast',
            'throttled': 'axi4_throttled'
        }

        profile = performance_map.get(performance_mode, 'axi4_normal')
        
        if component_type == 'master':
            return cls(master_profile=profile, slave_profile='axi4_normal')
        elif component_type == 'slave':
            return cls(master_profile='axi4_normal', slave_profile=profile)
        else:  # both
            return cls(master_profile=profile, slave_profile=profile)

    @classmethod
    def create_compliance_config(cls) -> 'AXI4TimingConfig':
        """
        Create a timing configuration optimized for compliance testing.

        Returns:
            AXI4TimingConfig instance with predictable, compliance-friendly timing
        """
        return cls(master_profile='compliance', slave_profile='compliance')

    @classmethod
    def create_from_constraints(cls, timing_constraints: Dict[str, tuple]) -> 'AXI4TimingConfig':
        """
        Create timing configuration from raw timing constraints.

        Args:
            timing_constraints: Dictionary of constraint name to (bins, weights) tuples

        Returns:
            AXI4TimingConfig instance with custom constraints
        """
        # Convert timing constraints to profile format
        custom_profiles = {}
        
        # Create profiles from constraints
        for constraint_name, constraint_value in timing_constraints.items():
            profile_name = f"custom_{constraint_name}"
            custom_profiles[profile_name] = constraint_value

        # Use the first custom profile as default
        default_profile = list(custom_profiles.keys())[0] if custom_profiles else 'axi4_normal'
        
        return cls(
            master_profile=default_profile,
            slave_profile=default_profile,
            custom_profiles=custom_profiles
        )

    @classmethod
    def create_channel_optimized(cls, channels: List[str], 
                               performance_mode: str = 'normal') -> 'AXI4TimingConfig':
        """
        Create timing configuration optimized for specific channels and performance.

        Args:
            channels: List of AXI4 channels to optimize for
            performance_mode: Performance optimization mode

        Returns:
            AXI4TimingConfig instance optimized for the channels and performance
        """
        # Start with performance-based config
        config = cls.create_performance_config(performance_mode, 'both')
        
        # Further optimize for specific channels
        return config.create_channel_specific_config(channels)

    # Utility methods

    def get_timing_summary(self) -> Dict[str, Any]:
        """
        Get a summary of the timing configuration.

        Returns:
            Dictionary with timing configuration summary
        """
        return {
            'master_profile': self.master_profile,
            'slave_profile': self.slave_profile,
            'master_constraints': self.all_profiles.get(self.master_profile),
            'slave_constraints': self.all_profiles.get(self.slave_profile),
            'total_profiles': len(self.all_profiles),
            'cached_randomizers': len(self._randomizer_cache)
        }

    def clear_cache(self):
        """Clear the randomizer cache."""
        self._randomizer_cache.clear()

    def get_master_delay(self, profile: str = None) -> int:
        """
        Get a random delay value for master-side timing.

        Args:
            profile: Profile to use (default: master_profile)

        Returns:
            Random delay value in cycles
        """
        if profile is None:
            profile = self.master_profile

        randomizer = self.get_channel_randomizer('AW', 'master', profile)
        return randomizer.get_delay()

    def get_slave_delay(self, profile: str = None) -> int:
        """
        Get a random delay value for slave-side timing.

        Args:
            profile: Profile to use (default: slave_profile)

        Returns:
            Random delay value in cycles
        """
        if profile is None:
            profile = self.slave_profile

        randomizer = self.get_channel_randomizer('AW', 'slave', profile)
        return randomizer.get_delay()


# Convenience factory functions

def create_axi4_timing_config(channels: List[str], performance_mode: str = 'normal') -> AXI4TimingConfig:
    """
    Convenience function to create AXI4 timing configuration.

    Args:
        channels: List of AXI4 channels
        performance_mode: 'fast', 'normal', 'bursty', 'throttled', or 'stress'

    Returns:
        AXI4TimingConfig instance
    """
    return AXI4TimingConfig.create_channel_optimized(channels, performance_mode)


def create_quick_axi4_timing(profile_name: str = 'axi4_normal') -> FlexRandomizer:
    """
    Quick way to get a single FlexRandomizer for AXI4 timing.

    Args:
        profile_name: Name of the timing profile

    Returns:
        FlexRandomizer instance
    """
    config = AXI4TimingConfig()
    
    # Get the timing constraints for the profile
    constraints = config.all_profiles.get(profile_name, config.all_profiles['axi4_normal'])
    
    # Create a simple randomizer with generic field name
    return FlexRandomizer({'timing_delay': constraints})


def create_axi4_timing_from_profile(master_profile: str, slave_profile: str = None) -> AXI4TimingConfig:
    """
    Create AXI4 timing configuration from profile names.

    Args:
        master_profile: Profile name for master timing
        slave_profile: Profile name for slave timing (defaults to master_profile)

    Returns:
        AXI4TimingConfig instance
    """
    if slave_profile is None:
        slave_profile = master_profile
        
    return AXI4TimingConfig(master_profile, slave_profile)


# Default timing configurations for common use cases

def get_default_master_timing() -> AXI4TimingConfig:
    """Get default timing configuration for AXI4 masters."""
    return AXI4TimingConfig.create_performance_config('normal', 'master')


def get_default_slave_timing() -> AXI4TimingConfig:
    """Get default timing configuration for AXI4 slaves."""
    return AXI4TimingConfig.create_performance_config('normal', 'slave')


def get_stress_timing() -> AXI4TimingConfig:
    """Get stress testing timing configuration."""
    return AXI4TimingConfig.create_performance_config('stress', 'both')


def get_compliance_timing() -> AXI4TimingConfig:
    """Get compliance testing timing configuration."""
    return AXI4TimingConfig.create_compliance_config()