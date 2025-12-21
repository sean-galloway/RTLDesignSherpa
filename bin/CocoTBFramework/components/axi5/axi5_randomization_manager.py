# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI5RandomizationManager
# Purpose: AXI5 Randomization Manager - Unified randomization management.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-16

"""
AXI5 Randomization Manager - Unified randomization management for AXI5 components.

This module provides the AXI5RandomizationManager class that unifies
protocol and timing randomization for optimal AXI5 verification.

Features:
- Unified randomization management
- Convenient methods for common patterns
- Support for AXI5-specific features (atomic, MTE, security)
- Enhanced dual randomization capabilities
"""

from typing import Dict, List, Optional, Any

from .axi5_randomization_config import AXI5RandomizationConfig, AXI5RandomizationProfile
from .axi5_timing_config import create_axi5_timing_from_profile, get_axi5_timing_profiles


class AXI5TimingConfig:
    """
    AXI5 timing configuration wrapper.

    Provides an interface compatible with the randomization manager.
    """

    def __init__(self, channels: Optional[List[str]] = None, performance_mode: str = 'normal'):
        """
        Initialize timing configuration.

        Args:
            channels: List of AXI5 channels
            performance_mode: Performance mode name
        """
        self.channels = channels or ['AW', 'W', 'B', 'AR', 'R']
        self.performance_mode = performance_mode

        # Map performance modes to timing profiles
        profile_mapping = {
            'fast': 'axi5_fast',
            'normal': 'axi5_normal',
            'slow': 'axi5_slow',
            'bursty': 'axi5_backtoback',
            'throttled': 'axi5_slow',
            'stress': 'axi5_stress',
            'atomic': 'axi5_atomic',
            'mte': 'axi5_mte',
            'secure': 'axi5_secure',
            'chunked': 'axi5_chunked',
        }

        profile_name = profile_mapping.get(performance_mode, 'axi5_normal')
        self._timing = create_axi5_timing_from_profile(profile_name)
        self._strict_handshakes = False
        self._burst_mode = False
        self._variable_delays = False

    def get_channel_configs(self, channels: Optional[List[str]] = None) -> Dict[str, Any]:
        """Get timing configurations for specified channels."""
        channels = channels or self.channels
        return {ch: self._timing for ch in channels}

    def get_master_profile(self) -> Dict[str, Any]:
        """Get timing profile optimized for master."""
        return self._timing

    def get_slave_profile(self) -> Dict[str, Any]:
        """Get timing profile optimized for slave."""
        return self._timing

    def get_monitor_profile(self) -> Dict[str, Any]:
        """Get timing profile optimized for monitor."""
        return self._timing

    def set_performance_mode(self, mode: str):
        """Update performance mode."""
        self.performance_mode = mode
        profile_mapping = {
            'fast': 'axi5_fast',
            'normal': 'axi5_normal',
            'slow': 'axi5_slow',
            'bursty': 'axi5_backtoback',
            'throttled': 'axi5_slow',
            'stress': 'axi5_stress',
            'atomic': 'axi5_atomic',
            'mte': 'axi5_mte',
            'secure': 'axi5_secure',
            'chunked': 'axi5_chunked',
        }
        profile_name = profile_mapping.get(mode, 'axi5_normal')
        self._timing = create_axi5_timing_from_profile(profile_name)

    def enable_strict_handshakes(self):
        """Enable strict handshake timing."""
        self._strict_handshakes = True

    def enable_burst_mode(self):
        """Enable burst-optimized timing."""
        self._burst_mode = True
        self._timing = create_axi5_timing_from_profile('axi5_backtoback')

    def enable_variable_delays(self):
        """Enable variable delay patterns."""
        self._variable_delays = True
        self._timing = create_axi5_timing_from_profile('axi5_stress')

    def get_statistics(self) -> Dict[str, Any]:
        """Get timing statistics."""
        return {
            'performance_mode': self.performance_mode,
            'channels': self.channels,
            'strict_handshakes': self._strict_handshakes,
            'burst_mode': self._burst_mode,
            'variable_delays': self._variable_delays,
        }


def create_axi5_timing_config(channels: Optional[List[str]] = None,
                               performance_mode: str = 'normal') -> AXI5TimingConfig:
    """
    Create AXI5 timing configuration.

    Args:
        channels: List of channels to configure
        performance_mode: Performance mode name

    Returns:
        AXI5TimingConfig instance
    """
    return AXI5TimingConfig(channels, performance_mode)


class AXI5RandomizationManager:
    """
    Manages both protocol and timing randomization for AXI5 components.

    This class provides a unified interface for managing both:
    - Protocol randomization (AXI5RandomizationConfig) for field values
    - Timing randomization (AXI5TimingConfig) for delays/patterns

    Includes support for AXI5-specific features like atomic operations,
    Memory Tagging Extension, and security contexts.
    """

    def __init__(self, protocol_config: Optional[AXI5RandomizationConfig] = None,
                 timing_config: Optional[AXI5TimingConfig] = None,
                 channels: Optional[List[str]] = None,
                 data_width: int = 32,
                 performance_mode: str = 'normal'):
        """
        Initialize unified randomization manager.

        Args:
            protocol_config: AXI5RandomizationConfig for field values (optional)
            timing_config: AXI5TimingConfig for timing patterns (optional)
            channels: List of AXI5 channels for timing configuration
            data_width: Data width for protocol configuration
            performance_mode: Performance mode for timing configuration
        """
        # Set up protocol randomization with sensible defaults
        self.protocol = protocol_config or AXI5RandomizationConfig()
        self.protocol.set_data_width(data_width)

        # Set up timing randomization with sensible defaults
        if timing_config is None:
            channels = channels or ['AW', 'W', 'B', 'AR', 'R']
            self.timing = create_axi5_timing_config(channels, performance_mode)
        else:
            self.timing = timing_config

        self.channels = channels or ['AW', 'W', 'B', 'AR', 'R']
        self.data_width = data_width
        self.performance_mode = performance_mode

        # Statistics
        self.stats = {
            'protocol_calls': 0,
            'timing_calls': 0,
            'configurations_created': 0,
            'atomic_configs': 0,
            'mte_configs': 0,
            'security_configs': 0,
        }

    def get_protocol_values(self, fields: Dict[str, Any]) -> Dict[str, Any]:
        """
        Get randomized protocol field values.

        Args:
            fields: Dictionary of field names and constraints

        Returns:
            Dictionary of randomized field values
        """
        self.stats['protocol_calls'] += 1
        return self.protocol.randomize_fields(fields)

    def get_timing_delays(self, channels: Optional[List[str]] = None) -> Dict[str, Any]:
        """
        Get timing delay patterns for specified channels.

        Args:
            channels: List of channel names (uses default if None)

        Returns:
            Dictionary of timing configurations per channel
        """
        self.stats['timing_calls'] += 1
        channels = channels or self.channels
        return self.timing.get_channel_configs(channels)

    def create_master_config(self, **kwargs) -> Dict[str, Any]:
        """Create optimized configuration for AXI5 Master."""
        self.stats['configurations_created'] += 1

        # Master-optimized protocol settings
        self.protocol.set_master_mode(True)
        self.protocol.set_error_injection_rate(0.0)

        # Master-optimized timing settings
        timing_config = self.timing.get_master_profile()

        return {
            'protocol_randomizer': self.protocol,
            'timing_randomizer': self.timing,
            'timing_config': timing_config,
            **kwargs
        }

    def create_slave_config(self, **kwargs) -> Dict[str, Any]:
        """Create optimized configuration for AXI5 Slave."""
        self.stats['configurations_created'] += 1

        # Slave-optimized protocol settings
        self.protocol.set_master_mode(False)
        self.protocol.set_error_injection_rate(0.01)

        # Slave-optimized timing settings
        timing_config = self.timing.get_slave_profile()

        return {
            'protocol_randomizer': self.protocol,
            'timing_randomizer': self.timing,
            'timing_config': timing_config,
            **kwargs
        }

    def create_monitor_config(self, **kwargs) -> Dict[str, Any]:
        """Create optimized configuration for AXI5 Monitor."""
        self.stats['configurations_created'] += 1

        timing_config = self.timing.get_monitor_profile()

        return {
            'timing_config': timing_config,
            **kwargs
        }

    def create_atomic_config(self, atomic_types: Optional[List[int]] = None, **kwargs) -> Dict[str, Any]:
        """
        Create configuration for atomic operations testing.

        Args:
            atomic_types: List of atomic operation types to enable
            **kwargs: Additional configuration parameters
        """
        self.stats['configurations_created'] += 1
        self.stats['atomic_configs'] += 1

        self.protocol.enable_atomic_operations(atomic_types)
        self.timing.set_performance_mode('atomic')

        return {
            'protocol_randomizer': self.protocol,
            'timing_randomizer': self.timing,
            'feature': 'atomic',
            **kwargs
        }

    def create_mte_config(self, tag_operations: Optional[List[int]] = None, **kwargs) -> Dict[str, Any]:
        """
        Create configuration for Memory Tagging Extension testing.

        Args:
            tag_operations: List of tag operations to enable
            **kwargs: Additional configuration parameters
        """
        self.stats['configurations_created'] += 1
        self.stats['mte_configs'] += 1

        self.protocol.enable_memory_tagging(tag_operations)
        self.timing.set_performance_mode('mte')

        return {
            'protocol_randomizer': self.protocol,
            'timing_randomizer': self.timing,
            'feature': 'mte',
            **kwargs
        }

    def create_security_config(self, **kwargs) -> Dict[str, Any]:
        """
        Create configuration for security context testing.

        Args:
            **kwargs: Additional configuration parameters
        """
        self.stats['configurations_created'] += 1
        self.stats['security_configs'] += 1

        self.protocol.enable_secure_access()
        self.timing.set_performance_mode('secure')

        return {
            'protocol_randomizer': self.protocol,
            'timing_randomizer': self.timing,
            'feature': 'security',
            **kwargs
        }

    def set_performance_mode(self, mode: str):
        """
        Update performance mode for timing randomization.

        Args:
            mode: 'fast', 'normal', 'bursty', 'throttled', 'stress',
                  'atomic', 'mte', 'secure', 'chunked'
        """
        self.performance_mode = mode
        self.timing.set_performance_mode(mode)

    def set_error_injection_rate(self, rate: float):
        """Set error injection rate for protocol randomization."""
        self.protocol.set_error_injection_rate(rate)

    def set_atomic_rate(self, rate: float):
        """Set atomic operation rate."""
        self.protocol.set_atomic_rate(rate)

    def set_mte_rate(self, rate: float):
        """Set Memory Tagging Extension rate."""
        self.protocol.set_mte_rate(rate)

    def set_security_rate(self, rate: float):
        """Set security context rate."""
        self.protocol.set_security_rate(rate)

    def configure_for_compliance_testing(self):
        """Configure for strict AXI5 protocol compliance testing."""
        self.protocol.set_profile(AXI5RandomizationProfile.COMPLIANCE)
        self.protocol.set_error_injection_rate(0.0)
        self.protocol.set_atomic_rate(0.0)
        self.protocol.set_mte_rate(0.0)

        self.timing.set_performance_mode('normal')
        self.timing.enable_strict_handshakes()

    def configure_for_performance_testing(self):
        """Configure for high-performance stress testing."""
        self.protocol.set_profile(AXI5RandomizationProfile.PERFORMANCE)

        self.timing.set_performance_mode('stress')
        self.timing.enable_burst_mode()

    def configure_for_atomic_testing(self):
        """Configure for atomic operations testing."""
        self.protocol.set_profile(AXI5RandomizationProfile.ATOMIC)
        self.protocol.enable_atomic_operations()

        self.timing.set_performance_mode('atomic')

    def configure_for_mte_testing(self):
        """Configure for Memory Tagging Extension testing."""
        self.protocol.set_profile(AXI5RandomizationProfile.MTE)
        self.protocol.enable_memory_tagging()

        self.timing.set_performance_mode('mte')

    def configure_for_security_testing(self):
        """Configure for security context testing."""
        self.protocol.set_profile(AXI5RandomizationProfile.SECURITY)
        self.protocol.enable_secure_access()

        self.timing.set_performance_mode('secure')

    def configure_for_error_injection(self, error_rate: float = 0.05):
        """Configure for error injection testing."""
        self.protocol.set_error_injection_rate(error_rate)

        self.timing.set_performance_mode('throttled')
        self.timing.enable_variable_delays()

    def get_statistics(self) -> Dict[str, Any]:
        """Get usage statistics."""
        return {
            **self.stats,
            'protocol_stats': self.protocol.get_statistics(),
            'timing_stats': self.timing.get_statistics()
        }

    def reset_statistics(self):
        """Reset all statistics counters."""
        self.stats = {key: 0 for key in self.stats}
        if hasattr(self.protocol, 'reset_statistics'):
            self.protocol.reset_statistics()


# Convenience factory functions

def create_unified_randomization(data_width: int = 32,
                                 channels: Optional[List[str]] = None,
                                 performance_mode: str = 'normal') -> AXI5RandomizationManager:
    """
    Create a unified randomization manager with sensible defaults.
    """
    return AXI5RandomizationManager(
        data_width=data_width,
        channels=channels,
        performance_mode=performance_mode
    )


def create_compliance_randomization(data_width: int = 32) -> AXI5RandomizationManager:
    """Create randomization manager configured for compliance testing."""
    manager = create_unified_randomization(data_width, performance_mode='normal')
    manager.configure_for_compliance_testing()
    return manager


def create_performance_randomization(data_width: int = 32) -> AXI5RandomizationManager:
    """Create randomization manager configured for performance testing."""
    manager = create_unified_randomization(data_width, performance_mode='stress')
    manager.configure_for_performance_testing()
    return manager


def create_atomic_randomization(data_width: int = 32) -> AXI5RandomizationManager:
    """Create randomization manager configured for atomic operations testing."""
    manager = create_unified_randomization(data_width, performance_mode='atomic')
    manager.configure_for_atomic_testing()
    return manager


def create_mte_randomization(data_width: int = 32) -> AXI5RandomizationManager:
    """Create randomization manager configured for MTE testing."""
    manager = create_unified_randomization(data_width, performance_mode='mte')
    manager.configure_for_mte_testing()
    return manager


def create_security_randomization(data_width: int = 32) -> AXI5RandomizationManager:
    """Create randomization manager configured for security testing."""
    manager = create_unified_randomization(data_width, performance_mode='secure')
    manager.configure_for_security_testing()
    return manager


def create_error_injection_randomization(data_width: int = 32,
                                         error_rate: float = 0.05) -> AXI5RandomizationManager:
    """Create randomization manager configured for error injection testing."""
    manager = create_unified_randomization(data_width, performance_mode='throttled')
    manager.configure_for_error_injection(error_rate)
    return manager
