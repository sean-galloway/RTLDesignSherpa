# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PerformanceMode
# Purpose: STREAM DMA Performance Analysis Core Module
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-18

"""
STREAM DMA Performance Analysis Core Module

Performance modeling for STREAM memory-to-memory DMA:
- Separate read and write paths (decoupled by SRAM buffer)
- Low/Medium/High performance modes
- Bandwidth scaling analysis
- SRAM buffer impact
"""

import pandas as pd
import numpy as np
from dataclasses import dataclass
from typing import Optional, Dict, List
from enum import Enum

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

MAX_CHANNELS = 8  # STREAM supports 8 independent channels

# AXI Interface Parameters
DEFAULT_W = 64              # Bus width in bytes/beat (512-bit interface)
DEFAULT_F = 1.0             # Frequency in GHz
DEFAULT_PAYLOAD_OPTIONS = [256, 512, 1024, 2048, 4096]  # Payload sizes in bytes
DEFAULT_PAYLOAD = 1024      # Default payload size in bytes
DEFAULT_ALPHA = 0.9         # Protocol efficiency factor
DEFAULT_LATENCY = 200       # Memory latency in cycles

# SRAM Configuration
DEFAULT_SRAM_TOTAL = 65536  # 64 KB total SRAM
DEFAULT_SRAM_PER_CHANNEL = 8192  # 8 KB per channel (128 lines × 64 bytes)
DEFAULT_SRAM_LINES_PER_CHANNEL = 128  # 128 lines per channel

# ============================================================================

class PerformanceMode(Enum):
    """STREAM Performance Modes"""
    LOW = "LOW"       # Tutorial: minimal logic, single outstanding
    MEDIUM = "MEDIUM" # Balanced: basic pipelining, 4 outstanding
    HIGH = "HIGH"     # Max throughput: full pipelining, 16 outstanding
    PERFECT = "PERFECT" # Ideal: unlimited resources to saturate bus


# Performance Mode Configurations
LOW_PERF_CONFIG = {
    'name': 'Low Performance',
    'max_burst_len_read': 8,      # 8-beat bursts for reads
    'max_burst_len_write': 16,    # 16-beat bursts for writes (asymmetric!)
    'max_outstanding_read': 1,    # Single outstanding read
    'max_outstanding_write': 1,   # Single outstanding write
    'pipeline_depth': 1,          # No pipelining
    'use_case': 'Tutorial, area-constrained'
}

MEDIUM_PERF_CONFIG = {
    'name': 'Medium Performance',
    'max_burst_len_read': 16,     # 16-beat bursts for reads
    'max_burst_len_write': 32,    # 32-beat bursts for writes
    'max_outstanding_read': 4,    # 4 outstanding reads
    'max_outstanding_write': 4,   # 4 outstanding writes
    'pipeline_depth': 4,          # Basic pipelining
    'use_case': 'Typical FPGA'
}

HIGH_PERF_CONFIG = {
    'name': 'High Performance',
    'max_burst_len_read': 256,    # Up to 256-beat bursts for reads
    'max_burst_len_write': 256,   # Up to 256-beat bursts for writes
    'max_outstanding_read': 16,   # 16 outstanding reads
    'max_outstanding_write': 16,  # 16 outstanding writes
    'pipeline_depth': 16,         # Full pipelining
    'use_case': 'High-throughput ASIC/FPGA'
}

PERFECT_PERF_CONFIG = {
    'name': 'Perfect (Theoretical)',
    'max_burst_len_read': 256,    # Up to 256-beat bursts for reads
    'max_burst_len_write': 256,   # Up to 256-beat bursts for writes
    'max_outstanding_read': 256,  # Unlimited outstanding (effectively)
    'max_outstanding_write': 256, # Unlimited outstanding (effectively)
    'pipeline_depth': 256,        # Unlimited pipeline depth
    'sram_lines_per_channel': 4096,  # Large SRAM (256 KB per channel)
    'use_case': 'Theoretical maximum (shows what would be needed to saturate)'
}


@dataclass
class AXIConfig:
    """
    Configuration for STREAM AXI4 performance analysis.

    STREAM Architecture:
    - Separate AXI read and write engines (decoupled by SRAM)
    - Read engine: Fetches source data from memory → SRAM
    - Write engine: Drains SRAM → destination memory
    - SRAM: 64 KB total, partitioned into 8 channels (8 KB each)

    Performance Modes:
    - Low: Single outstanding, small bursts (tutorial)
    - Medium: 4 outstanding, medium bursts (typical)
    - High: 16 outstanding, large bursts (max throughput)

    Key Difference from RAPIDS:
    - Read and write are INDEPENDENT (not network-tied)
    - Can analyze read and write bandwidth separately
    - SRAM buffer decouples timing between paths
    """

    # Payload and interface
    payload: int = DEFAULT_PAYLOAD
    W: int = DEFAULT_W
    f: float = DEFAULT_F
    alpha: float = DEFAULT_ALPHA
    latency: int = DEFAULT_LATENCY

    # Performance mode parameters
    max_burst_len: int = 16        # Max burst length in beats
    max_outstanding: int = 1       # Max outstanding transactions
    pipeline_depth: int = 1        # Pipeline depth

    # SRAM configuration
    sram_lines_per_channel: int = DEFAULT_SRAM_LINES_PER_CHANNEL
    sram_per_channel: int = DEFAULT_SRAM_PER_CHANNEL

    # Engine type (read or write)
    engine_type: str = "read"      # "read" or "write"

    def __post_init__(self):
        """Calculate derived parameters"""
        self.BL = self.payload / self.W  # Burst length in beats
        self.Bmax = self.W * self.f * self.alpha  # Peak bandwidth (GB/s)

        # Effective burst length (limited by max_burst_len)
        self.effective_BL = min(self.BL, self.max_burst_len)

        # SRAM capacity in bursts (per channel)
        self.sram_capacity_bursts = int(self.sram_lines_per_channel / self.effective_BL)

        # Effective pipeline depth (limited by SRAM capacity and max_outstanding)
        self.effective_pipeline = min(
            self.pipeline_depth,
            self.sram_capacity_bursts,
            self.max_outstanding
        )


class AXI4Performance:
    """Performance analysis for STREAM AXI4 engines"""

    def __init__(self, config: AXIConfig):
        self.config = config

    def calculate_channel_bandwidth(self, num_channels: int) -> Dict:
        """
        Calculate bandwidth for given number of channels.

        STREAM Read Path:
        - Issue AR transaction (latency cycles)
        - Receive R data (BL cycles)
        - Write to SRAM (concurrent with R)
        - Time per burst = latency + BL (with pipelining)

        STREAM Write Path:
        - Read from SRAM (concurrent with AW/W)
        - Issue AW transaction (latency cycles)
        - Stream W data (BL cycles)
        - Wait for B response (negligible)
        - Time per burst = latency + BL (with pipelining)

        With pipelining:
        - Multiple bursts in flight
        - Effective rate = payload / (latency + BL)

        Without pipelining (pipeline_depth=1):
        - Sequential: latency + BL per burst

        Limits:
        1. Timing (latency + data transfer)
        2. AXI peak bandwidth
        3. SRAM capacity (limits effective pipelining)
        4. Outstanding transaction limit
        """
        cfg = self.config

        # Effective channels (STREAM has max 8)
        effective_channels = min(num_channels, MAX_CHANNELS)

        # Calculate per-channel bandwidth
        if cfg.effective_pipeline > 1:
            # With pipelining: multiple bursts in flight
            # Effective rate approaches: payload / (latency/depth + BL)
            cycles_per_burst = (cfg.latency / cfg.effective_pipeline) + cfg.effective_BL
        else:
            # No pipelining: sequential operation
            cycles_per_burst = cfg.latency + cfg.effective_BL

        # Per-channel bandwidth (GB/s)
        B_channel = (cfg.payload * cfg.f) / cycles_per_burst

        # Total bandwidth from all channels
        total_bw_from_channels = B_channel * effective_channels

        # Apply system-wide limits
        total_bw = min(total_bw_from_channels, cfg.Bmax)

        # Determine limiting factor
        if total_bw == cfg.Bmax:
            limited_by = "AXI_peak"
        elif cfg.effective_pipeline < cfg.pipeline_depth:
            if cfg.effective_pipeline == cfg.sram_capacity_bursts:
                limited_by = "SRAM_capacity"
            else:
                limited_by = "max_outstanding"
        else:
            limited_by = "timing"

        efficiency = (total_bw / cfg.Bmax) * 100
        saturated = efficiency >= 99.9

        return {
            'num_channels': num_channels,
            'effective_channels': effective_channels,
            'pipeline_depth': cfg.pipeline_depth,
            'effective_pipeline': cfg.effective_pipeline,
            'max_outstanding': cfg.max_outstanding,
            'burst_length': cfg.effective_BL,
            'B_channel': B_channel,
            'total_bw': total_bw,
            'efficiency': efficiency,
            'saturated': saturated,
            'limited_by': limited_by,
            'cycles_per_burst': cycles_per_burst,
            'engine_type': cfg.engine_type
        }

    def generate_performance_table(self, max_channels: int = MAX_CHANNELS) -> pd.DataFrame:
        """Generate performance table for range of channel counts"""
        results = []

        for n in range(1, max_channels + 1):
            perf = self.calculate_channel_bandwidth(n)

            row = {
                'Channels': perf['num_channels'],
                'Effective_Channels': perf['effective_channels'],
                'Pipeline_Depth': perf['pipeline_depth'],
                'Effective_Pipeline': perf['effective_pipeline'],
                'Max_Outstanding': perf['max_outstanding'],
                'Burst_Length': perf['burst_length'],
                'BW_per_Channel_GBps': perf['B_channel'],
                'Total_BW_GBps': perf['total_bw'],
                'Efficiency_%': perf['efficiency'],
                'Saturated': perf['saturated'],
                'Limited_By': perf['limited_by'],
                'Cycles_per_Burst': perf['cycles_per_burst'],
                'Engine_Type': perf['engine_type']
            }

            results.append(row)

        return pd.DataFrame(results)

    def compare_payloads(self, max_channels: int = MAX_CHANNELS,
                        payloads: Optional[List[int]] = None) -> Dict[int, pd.DataFrame]:
        """Compare performance across different payload sizes"""
        if payloads is None:
            payloads = DEFAULT_PAYLOAD_OPTIONS

        results = {}
        original_payload = self.config.payload
        original_BL = self.config.BL

        for payload in payloads:
            self.config.payload = payload
            self.config.BL = payload / self.config.W
            self.config.__post_init__()  # Recalculate derived params
            results[payload] = self.generate_performance_table(max_channels)

        # Restore original
        self.config.payload = original_payload
        self.config.BL = original_BL
        self.config.__post_init__()

        return results


@dataclass
class StreamDMAConfig:
    """Configuration for complete STREAM DMA (read + write paths)"""

    read_config: AXIConfig
    write_config: AXIConfig

    def __post_init__(self):
        """Validate configurations"""
        assert self.read_config.Bmax == self.write_config.Bmax, \
            "Read and write configs must have same peak bandwidth"
        assert self.read_config.engine_type == "read", \
            "read_config must have engine_type='read'"
        assert self.write_config.engine_type == "write", \
            "write_config must have engine_type='write'"


class StreamDMAPerformance:
    """Performance analysis for complete STREAM DMA (read + write)"""

    def __init__(self, config: StreamDMAConfig):
        self.config = config
        self.read_perf = AXI4Performance(config.read_config)
        self.write_perf = AXI4Performance(config.write_config)

    def calculate_dma_bandwidth(self, num_channels: int) -> Dict:
        """
        Calculate DMA bandwidth for given number of channels.

        STREAM DMA end-to-end:
        - Read path: Memory (source) → AXI read → SRAM
        - Write path: SRAM → AXI write → Memory (destination)

        Paths are INDEPENDENT but share SRAM buffer.
        Overall DMA throughput limited by slower of read or write.

        Returns separate read and write bandwidth plus effective DMA throughput.
        """
        read_result = self.read_perf.calculate_channel_bandwidth(num_channels)
        write_result = self.write_perf.calculate_channel_bandwidth(num_channels)

        # DMA throughput limited by slower path
        dma_throughput = min(read_result['total_bw'], write_result['total_bw'])

        # Determine bottleneck
        if read_result['total_bw'] < write_result['total_bw']:
            bottleneck = "read_path"
        elif write_result['total_bw'] < read_result['total_bw']:
            bottleneck = "write_path"
        else:
            bottleneck = "balanced"

        return {
            'num_channels': num_channels,
            'read_bw': read_result['total_bw'],
            'write_bw': write_result['total_bw'],
            'dma_throughput': dma_throughput,
            'bottleneck': bottleneck,
            'read_limited_by': read_result['limited_by'],
            'write_limited_by': write_result['limited_by'],
            'read_efficiency': read_result['efficiency'],
            'write_efficiency': write_result['efficiency']
        }

    def generate_dma_table(self, max_channels: int = MAX_CHANNELS) -> pd.DataFrame:
        """Generate DMA performance table"""
        results = []

        for n in range(1, max_channels + 1):
            perf = self.calculate_dma_bandwidth(n)
            results.append({
                'Channels': perf['num_channels'],
                'Read_BW_GBps': perf['read_bw'],
                'Write_BW_GBps': perf['write_bw'],
                'DMA_Throughput_GBps': perf['dma_throughput'],
                'Bottleneck': perf['bottleneck'],
                'Read_Limited_By': perf['read_limited_by'],
                'Write_Limited_By': perf['write_limited_by'],
                'Read_Efficiency_%': perf['read_efficiency'],
                'Write_Efficiency_%': perf['write_efficiency']
            })

        return pd.DataFrame(results)


def show_defaults():
    """Print current default configuration values"""
    print("="*70)
    print("  STREAM DMA PERFORMANCE MODEL - DEFAULT CONFIGURATION")
    print("="*70)
    print(f"\n  Max Channels:        {MAX_CHANNELS}")
    print(f"\n  AXI Interface:")
    print(f"    Width (W):         {DEFAULT_W} bytes/beat (512-bit)")
    print(f"    Frequency (f):     {DEFAULT_F} GHz")
    print(f"    Payload Options:   {DEFAULT_PAYLOAD_OPTIONS} bytes")
    print(f"    Default Payload:   {DEFAULT_PAYLOAD} bytes")
    print(f"    Alpha:             {DEFAULT_ALPHA}")
    print(f"    Latency:           {DEFAULT_LATENCY} cycles")
    print(f"    Peak Bandwidth:    {DEFAULT_W * DEFAULT_F * DEFAULT_ALPHA:.2f} GB/s")

    print(f"\n  SRAM Configuration:")
    print(f"    Total Size:        {DEFAULT_SRAM_TOTAL} bytes (64 KB)")
    print(f"    Per Channel:       {DEFAULT_SRAM_PER_CHANNEL} bytes (8 KB)")
    print(f"    Lines per Channel: {DEFAULT_SRAM_LINES_PER_CHANNEL}")

    print(f"\n  Performance Modes:")
    for mode_name, mode_config in [
        ('LOW', LOW_PERF_CONFIG),
        ('MEDIUM', MEDIUM_PERF_CONFIG),
        ('HIGH', HIGH_PERF_CONFIG),
        ('PERFECT', PERFECT_PERF_CONFIG)
    ]:
        print(f"\n    {mode_name} ({mode_config['use_case']}):")
        print(f"      Read Burst Len:     {mode_config['max_burst_len_read']} beats")
        print(f"      Write Burst Len:    {mode_config['max_burst_len_write']} beats")
        print(f"      Max Outstanding:    {mode_config['max_outstanding_read']} (read), {mode_config['max_outstanding_write']} (write)")
        print(f"      Pipeline Depth:     {mode_config['pipeline_depth']}")
        if 'sram_lines_per_channel' in mode_config:
            print(f"      SRAM per Channel:   {mode_config['sram_lines_per_channel']} lines ({mode_config['sram_lines_per_channel'] * 64 // 1024} KB)")

    print("="*70 + "\n")


def create_mode_configs(mode: PerformanceMode, payload: int = DEFAULT_PAYLOAD) -> StreamDMAConfig:
    """
    Create read and write configs for specified performance mode.

    Args:
        mode: PerformanceMode enum (LOW, MEDIUM, HIGH, PERFECT)
        payload: Burst size in bytes

    Returns:
        StreamDMAConfig with read and write configurations
    """
    if mode == PerformanceMode.LOW:
        mode_cfg = LOW_PERF_CONFIG
    elif mode == PerformanceMode.MEDIUM:
        mode_cfg = MEDIUM_PERF_CONFIG
    elif mode == PerformanceMode.HIGH:
        mode_cfg = HIGH_PERF_CONFIG
    elif mode == PerformanceMode.PERFECT:
        mode_cfg = PERFECT_PERF_CONFIG
    else:
        raise ValueError(f"Unknown performance mode: {mode}")

    # Get SRAM configuration (PERFECT mode has custom SRAM)
    sram_lines = mode_cfg.get('sram_lines_per_channel', DEFAULT_SRAM_LINES_PER_CHANNEL)
    sram_per_channel = sram_lines * DEFAULT_W  # lines × bytes per line

    # Create read engine config
    read_config = AXIConfig(
        payload=payload,
        max_burst_len=mode_cfg['max_burst_len_read'],
        max_outstanding=mode_cfg['max_outstanding_read'],
        pipeline_depth=mode_cfg['pipeline_depth'],
        sram_lines_per_channel=sram_lines,
        sram_per_channel=sram_per_channel,
        engine_type="read"
    )

    # Create write engine config
    write_config = AXIConfig(
        payload=payload,
        max_burst_len=mode_cfg['max_burst_len_write'],
        max_outstanding=mode_cfg['max_outstanding_write'],
        pipeline_depth=mode_cfg['pipeline_depth'],
        sram_lines_per_channel=sram_lines,
        sram_per_channel=sram_per_channel,
        engine_type="write"
    )

    return StreamDMAConfig(read_config=read_config, write_config=write_config)
