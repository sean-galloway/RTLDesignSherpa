"""
STREAM DMA Performance Analysis Package

Core modules for modeling STREAM DMA performance across Low, Medium, and High
performance modes.
"""

from .performance import (
    AXIConfig,
    AXI4Performance,
    StreamDMAConfig,
    StreamDMAPerformance,
    PerformanceMode,
    LOW_PERF_CONFIG,
    MEDIUM_PERF_CONFIG,
    HIGH_PERF_CONFIG,
    PERFECT_PERF_CONFIG,
    DEFAULT_PAYLOAD_OPTIONS,
    show_defaults,
    create_mode_configs
)

from .visualization import PerformanceGraphs

__all__ = [
    'AXIConfig',
    'AXI4Performance',
    'StreamDMAConfig',
    'StreamDMAPerformance',
    'PerformanceMode',
    'LOW_PERF_CONFIG',
    'MEDIUM_PERF_CONFIG',
    'HIGH_PERF_CONFIG',
    'PERFECT_PERF_CONFIG',
    'DEFAULT_PAYLOAD_OPTIONS',
    'show_defaults',
    'create_mode_configs',
    'PerformanceGraphs'
]
