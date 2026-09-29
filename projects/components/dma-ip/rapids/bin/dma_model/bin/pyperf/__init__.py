"""
PyPerf: AXI4 Performance Analysis Library

Analytical performance modeling for AXI4 memory interfaces.

Main classes:
- AXIConfig: Configuration for AXI4 interface
- AXI4Performance: Performance calculator
- MixedAXIConfig: Mixed read/write configuration
- MixedAXI4Performance: Mixed workload analysis
- PerformanceGraphs: Visualization tools

Usage:
    from pyperf import AXIConfig, AXI4Performance
    
    config = AXIConfig(payload=2048, pipeline_depth=4)
    perf = AXI4Performance(config)
    results = perf.generate_performance_table(max_channels=16)
"""

from .performance import (
    AXIConfig,
    AXI4Performance,
    MixedAXIConfig,
    MixedAXI4Performance,
    show_defaults,
    # Constants
    MAX_CHANNELS,
    DEFAULT_W,
    DEFAULT_F,
    DEFAULT_PAYLOAD_OPTIONS,
    DEFAULT_PAYLOAD,
    DEFAULT_ALPHA,
    DEFAULT_LATENCY,
    DEFAULT_PIPELINE_DEPTH,
    DEFAULT_CYCLES_PER_BEAT,
    DEFAULT_PIPELINING_ENABLED,
    DEFAULT_STREAMING_DRAIN,
    DEFAULT_SRAM_MODE,
    DEFAULT_TOTAL_SRAM_SIZE,
    DEFAULT_SRAM_SLOT_SIZE,
    DEFAULT_MAX_CUSTOM_CHANNELS,
    DEFAULT_PER_CHANNEL_CAP
)

from .visualization import PerformanceGraphs

__version__ = "1.0.0"
__all__ = [
    # Main classes
    'AXIConfig',
    'AXI4Performance',
    'MixedAXIConfig',
    'MixedAXI4Performance',
    'PerformanceGraphs',
    'show_defaults',
    # Constants
    'MAX_CHANNELS',
    'DEFAULT_W',
    'DEFAULT_F',
    'DEFAULT_PAYLOAD_OPTIONS',
    'DEFAULT_PAYLOAD',
    'DEFAULT_ALPHA',
    'DEFAULT_LATENCY',
    'DEFAULT_PIPELINE_DEPTH',
    'DEFAULT_CYCLES_PER_BEAT',
    'DEFAULT_PIPELINING_ENABLED',
    'DEFAULT_STREAMING_DRAIN',
    'DEFAULT_SRAM_MODE',
    'DEFAULT_TOTAL_SRAM_SIZE',
    'DEFAULT_SRAM_SLOT_SIZE',
    'DEFAULT_MAX_CUSTOM_CHANNELS',
    'DEFAULT_PER_CHANNEL_CAP'
]
