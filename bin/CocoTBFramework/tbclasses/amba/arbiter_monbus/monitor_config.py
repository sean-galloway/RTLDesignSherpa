# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: TestResult
# Purpose: Centralized Monitor Configuration and Test Infrastructure
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Centralized Monitor Configuration and Test Infrastructure

This module provides:
- MonitorConfig class with all standard configurations
- TestResult dataclass for standardized test reporting
- Common utilities and validation functions

All type definitions are imported from the synchronized monbus_types.py file.
"""

from dataclasses import dataclass
from typing import Dict, List, Optional, Any, Union

# ✅ IMPORT ALL TYPES FROM SYNCHRONIZED monbus_types.py
from CocoTBFramework.tbclasses.monbus.monbus_types import (
    ProtocolType, PktType,
    # ARB Protocol event codes
    ARBErrorCode, ARBTimeoutCode, ARBCompletionCode, ARBThresholdCode,
    ARBPerformanceCode, ARBDebugCode,
    # AXI Protocol event codes
    AXIErrorCode, AXITimeoutCode,
    # APB Protocol event codes
    APBErrorCode,
    # Helper functions
    is_valid_protocol_type, is_valid_packet_type, get_event_code_enum,
    is_valid_event_code, get_event_code_name, get_protocol_name, get_packet_type_name
)


# =============================================================================
# STANDARDIZED TEST RESULT STRUCTURE
# =============================================================================

@dataclass
class TestResult:
    """Standardized test result structure used across all test modules"""
    passed: bool
    name: str
    details: str
    packets_collected: int = 0
    error_msg: str = ""
    execution_time_ns: Optional[float] = None
    debug_info: Optional[Dict[str, Any]] = None

    def __post_init__(self):
        """Validate test result after initialization"""
        if not isinstance(self.passed, bool):
            raise ValueError("passed must be a boolean")
        if not self.name:
            raise ValueError("name cannot be empty")


# Note: Packet type masking is now handled by PktType.get_mask() in monbus_types.py


# =============================================================================
# CENTRALIZED MONITOR CONFIGURATION CLASS
# =============================================================================

class MonitorConfig:
    """
    Centralized Monitor Configuration Class

    This replaces all the individual MonitorConfig classes in test files.
    Provides standard configurations and validation.
    """

    def __init__(self, enable: bool = True, pkt_type_enable: int = 0xFFFF,
                latency_thresh: int = 50, starvation_thresh: int = 100,
                fairness_thresh: int = 80, active_thresh: int = 8,
                ack_timeout_thresh: int = 64, efficiency_thresh: int = 75,
                sample_period: int = 32):
        """
        Initialize monitor configuration

        Args:
            enable: Enable/disable monitor
            pkt_type_enable: Packet type enable mask (16 bits)
            latency_thresh: Latency threshold (cycles)
            starvation_thresh: Starvation threshold (cycles)
            fairness_thresh: Fairness deviation threshold (%)
            active_thresh: Active request count threshold
            ack_timeout_thresh: ACK timeout threshold (cycles)
            efficiency_thresh: Efficiency threshold (%)
            sample_period: Sampling period (cycles)
        """
        self.enable = enable
        self.pkt_type_enable = pkt_type_enable
        self.latency_thresh = latency_thresh
        self.starvation_thresh = starvation_thresh
        self.fairness_thresh = fairness_thresh
        self.active_thresh = active_thresh
        self.ack_timeout_thresh = ack_timeout_thresh
        self.efficiency_thresh = efficiency_thresh
        self.sample_period = sample_period

        # Validate configuration
        self._validate()

    def _validate(self):
        """Validate configuration parameters"""
        if self.starvation_thresh < 1:
            raise ValueError(f"starvation_thresh too small: {self.starvation_thresh} (min 1)")
        if self.starvation_thresh > 65535:
            raise ValueError(f"starvation_thresh too large: {self.starvation_thresh} (max 65535)")
        if self.latency_thresh > 65535:
            raise ValueError(f"latency_thresh too large: {self.latency_thresh} (max 65535)")
        if self.sample_period < 1:
            raise ValueError(f"sample_period too small: {self.sample_period} (min 1)")
        if self.sample_period > 65535:
            raise ValueError(f"sample_period too large: {self.sample_period} (max 65535)")

    def copy(self, **overrides) -> 'MonitorConfig':
        """Create a copy with optional parameter overrides"""
        params = {
            'enable': self.enable,
            'pkt_type_enable': self.pkt_type_enable,
            'latency_thresh': self.latency_thresh,
            'starvation_thresh': self.starvation_thresh,
            'fairness_thresh': self.fairness_thresh,
            'active_thresh': self.active_thresh,
            'ack_timeout_thresh': self.ack_timeout_thresh,
            'efficiency_thresh': self.efficiency_thresh,
            'sample_period': self.sample_period,
        }
        params.update(overrides)
        return MonitorConfig(**params)

    def __str__(self) -> str:
        """String representation for debugging"""
        return (f"MonitorConfig(enable={self.enable}, "
                f"pkt_type=0x{self.pkt_type_enable:04x}, "
                f"starvation_thresh={self.starvation_thresh}, "
                f"sample_period={self.sample_period})")

    def __repr__(self) -> str:
        """Detailed representation"""
        return (f"MonitorConfig(enable={self.enable}, "
                f"pkt_type_enable=0x{self.pkt_type_enable:04x}, "
                f"latency_thresh={self.latency_thresh}, "
                f"starvation_thresh={self.starvation_thresh}, "
                f"fairness_thresh={self.fairness_thresh}, "
                f"active_thresh={self.active_thresh}, "
                f"ack_timeout_thresh={self.ack_timeout_thresh}, "
                f"efficiency_thresh={self.efficiency_thresh}, "
                f"sample_period={self.sample_period})")

    # =================================================================
    # STANDARD CONFIGURATION PRESETS
    # =================================================================

    @classmethod
    def disabled(cls) -> 'MonitorConfig':
        """Completely disabled monitor configuration"""
        return cls(enable=False, pkt_type_enable=0x0000)

    @classmethod
    def basic(cls) -> 'MonitorConfig':
        """Basic configuration for general testing"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(
                PktType.PktTypeError,
                PktType.PktTypeTimeout,
                PktType.PktTypeCompletion,
                PktType.PktTypeThreshold
            ),  # 0x000F
            latency_thresh=100,
            starvation_thresh=200,
            sample_period=32
        )

    @classmethod
    def comprehensive(cls) -> 'MonitorConfig':
        """Comprehensive configuration enabling all packet types"""
        return cls(
            enable=True,
            pkt_type_enable=0xFFFF,  # All packet types
            latency_thresh=50,
            starvation_thresh=100,
            fairness_thresh=60,
            active_thresh=8,
            ack_timeout_thresh=32,
            efficiency_thresh=70,
            sample_period=16
        )

    @classmethod
    def stress(cls) -> 'MonitorConfig':
        """Stress configuration with low thresholds for maximum packet generation"""
        return cls(
            enable=True,
            pkt_type_enable=0xFFFF,
            latency_thresh=10,
            starvation_thresh=25,
            fairness_thresh=15,
            active_thresh=2,
            ack_timeout_thresh=8,
            efficiency_thresh=30,
            sample_period=8
        )

    @classmethod
    def minimal(cls) -> 'MonitorConfig':
        """Minimal configuration with lowest possible thresholds"""
        return cls(
            enable=True,
            pkt_type_enable=0xFFFF,
            latency_thresh=1,
            starvation_thresh=1,
            fairness_thresh=1,
            active_thresh=1,
            ack_timeout_thresh=1,
            efficiency_thresh=1,
            sample_period=1
        )

    @classmethod
    def maximal(cls) -> 'MonitorConfig':
        """Maximal configuration with highest possible thresholds"""
        return cls(
            enable=True,
            pkt_type_enable=0xFFFF,
            latency_thresh=255,
            starvation_thresh=255,
            fairness_thresh=255,
            active_thresh=255,
            ack_timeout_thresh=255,
            efficiency_thresh=99,  # Efficiency is percentage
            sample_period=255
        )

    # =================================================================
    # SPECIFIC USE CASE CONFIGURATIONS
    # =================================================================

    @classmethod
    def for_latency_stress(cls) -> 'MonitorConfig':
        """Configuration optimized for latency stress testing"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(
                PktType.PktTypeThreshold,
                PktType.PktTypeError
            ),
            latency_thresh=15,  # Low threshold to trigger easily
            starvation_thresh=100,
            sample_period=16
        )

    @classmethod
    def for_starvation_detection(cls) -> 'MonitorConfig':
        """Configuration optimized for starvation detection"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(
                PktType.PktTypeError,
                PktType.PktTypeThreshold
            ),
            starvation_thresh=25,  # Low threshold
            sample_period=16
        )

    @classmethod
    def for_fairness_monitoring(cls) -> 'MonitorConfig':
        """Configuration optimized for fairness monitoring"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(
                PktType.PktTypeThreshold,
                PktType.PktTypeError
            ),
            fairness_thresh=30,  # Low threshold
            sample_period=16
        )

    @classmethod
    def for_active_monitoring(cls) -> 'MonitorConfig':
        """Configuration optimized for active request monitoring"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(PktType.PktTypeThreshold),
            active_thresh=4,  # Low threshold
            sample_period=8
        )

    @classmethod
    def for_efficiency_monitoring(cls) -> 'MonitorConfig':
        """Configuration optimized for efficiency monitoring"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(PktType.PktTypeThreshold),
            efficiency_thresh=90,  # High threshold - triggers when efficiency is low
            sample_period=16
        )

    @classmethod
    def for_timeout_detection(cls) -> 'MonitorConfig':
        """Configuration optimized for timeout detection"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(
                PktType.PktTypeTimeout,
                PktType.PktTypeError
            ),
            ack_timeout_thresh=16,  # Low threshold
            sample_period=8
        )

    @classmethod
    def for_protocol_monitoring(cls) -> 'MonitorConfig':
        """Configuration optimized for protocol monitoring"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(
                PktType.PktTypeError,
                PktType.PktTypeDebug
            ),
            sample_period=16
        )

    @classmethod
    def for_comprehensive_error_monitoring(cls) -> 'MonitorConfig':
        """Configuration for comprehensive error monitoring"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(
                PktType.PktTypeError,
                PktType.PktTypeTimeout,
                PktType.PktTypeDebug
            ),
            starvation_thresh=50,
            ack_timeout_thresh=32,
            sample_period=16
        )

    @classmethod
    def for_performance_monitoring(cls) -> 'MonitorConfig':
        """Configuration optimized for performance monitoring"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(
                PktType.PktTypePerf,
                PktType.PktTypeCompletion
            ),
            sample_period=16,
            efficiency_thresh=50
        )

    @classmethod
    def for_grant_tracking(cls) -> 'MonitorConfig':
        """Configuration optimized for grant tracking"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(PktType.PktTypeCompletion),
            sample_period=8
        )

    @classmethod
    def for_ack_tracking(cls) -> 'MonitorConfig':
        """Configuration optimized for ACK tracking"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(PktType.PktTypeCompletion),
            sample_period=8
        )

    @classmethod
    def for_throughput_monitoring(cls) -> 'MonitorConfig':
        """Configuration optimized for throughput monitoring"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(PktType.PktTypePerf),
            sample_period=16,
            efficiency_thresh=60
        )

    @classmethod
    def for_latency_performance(cls) -> 'MonitorConfig':
        """Configuration optimized for latency performance tracking"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(PktType.PktTypePerf),
            latency_thresh=30,
            sample_period=16
        )

    @classmethod
    def for_extended_operation(cls) -> 'MonitorConfig':
        """Configuration optimized for extended operation testing"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(
                PktType.PktTypeError,
                PktType.PktTypePerf,
                PktType.PktTypeCompletion
            ),
            latency_thresh=60,
            starvation_thresh=120,
            sample_period=32
        )

    @classmethod
    def maximum_rate(cls) -> 'MonitorConfig':
        """Configuration for maximum packet generation rate"""
        return cls(
            enable=True,
            pkt_type_enable=0xFFFF,  # All packet types
            latency_thresh=5,
            starvation_thresh=10,
            fairness_thresh=8,
            active_thresh=1,
            ack_timeout_thresh=4,
            efficiency_thresh=20,
            sample_period=4
        )

    # =================================================================
    # FILTER-SPECIFIC CONFIGURATIONS
    # =================================================================

    @classmethod
    def for_error_only(cls) -> 'MonitorConfig':
        """Configuration for ERROR packets only"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(PktType.PktTypeError),
            starvation_thresh=50,
            sample_period=16
        )

    @classmethod
    def for_performance_only(cls) -> 'MonitorConfig':
        """Configuration for PERFORMANCE packets only"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(PktType.PktTypePerf),
            sample_period=16,
            efficiency_thresh=50
        )

    @classmethod
    def for_threshold_only(cls) -> 'MonitorConfig':
        """Configuration for THRESHOLD packets only"""
        return cls(
            enable=True,
            pkt_type_enable=PktType.get_mask(PktType.PktTypeThreshold),
            latency_thresh=40,
            starvation_thresh=80,
            fairness_thresh=50,
            active_thresh=6,
            sample_period=16
        )


# =============================================================================
# CONFIGURATION UTILITIES
# =============================================================================

class ConfigUtils:
    """Utility functions for monitor configuration"""

    @staticmethod
    def get_packet_type_names(pkt_type_enable: int) -> List[str]:
        """Get list of enabled packet type names"""
        names = []
        if pkt_type_enable & (1 << PktType.PktTypeError):
            names.append("ERROR")
        if pkt_type_enable & (1 << PktType.PktTypeTimeout):
            names.append("TIMEOUT")
        if pkt_type_enable & (1 << PktType.PktTypeCompletion):
            names.append("COMPLETION")
        if pkt_type_enable & (1 << PktType.PktTypeThreshold):
            names.append("THRESHOLD")
        if pkt_type_enable & (1 << PktType.PktTypePerf):
            names.append("PERF")
        if pkt_type_enable & (1 << PktType.PktTypeDebug):
            names.append("DEBUG")
        return names

    @staticmethod
    def validate_config_consistency(config: MonitorConfig) -> List[str]:
        """Validate configuration for logical consistency"""
        warnings = []

        # Check if thresholds make sense relative to each other
        if config.starvation_thresh < config.latency_thresh:
            warnings.append("starvation_thresh < latency_thresh may cause conflicts")

        # Check if sample period is reasonable for thresholds
        if config.sample_period > config.starvation_thresh:
            warnings.append("sample_period > starvation_thresh may miss events")

        # Check if performance monitoring is enabled but sample period is too large
        if (config.pkt_type_enable & (1 << PktType.PktTypePerf)) and config.sample_period > 64:
            warnings.append("Large sample_period may reduce performance monitoring accuracy")

        return warnings
