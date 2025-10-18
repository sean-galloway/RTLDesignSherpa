# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIConfig
# Purpose: AXI4 Performance Analysis Core Module
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Performance Analysis Core Module

Core performance modeling for AXI4 interfaces including:
- Bandwidth scaling analysis
- Store-and-Forward vs Streaming drain modes
- Ping-Pong vs Monolithic SRAM modes
- Pipeline depth requirements
- Custom side capacity constraints
"""

import pandas as pd
import numpy as np
from dataclasses import dataclass
from typing import Optional, Dict, List

# ============================================================================
# GLOBAL CONFIGURATION - Edit these to change defaults for all analyses
# ============================================================================

MAX_CHANNELS = 32

# AXI Interface Parameters
DEFAULT_W = 64              # Bus width in bytes/beat (512-bit interface)
DEFAULT_F = 1.0             # Frequency in GHz
DEFAULT_PAYLOAD_OPTIONS = [256, 512, 1024, 2048]  # Available payload sizes in bytes
DEFAULT_PAYLOAD = 2048      # Default payload size in bytes
DEFAULT_ALPHA = 0.9         # Protocol efficiency factor
DEFAULT_LATENCY = 200       # Memory latency in cycles

# Pipelining Parameters
DEFAULT_PIPELINE_DEPTH = 1           # Pipeline depth (1 = no pipelining)
DEFAULT_CYCLES_PER_BEAT = 16         # Drain rate: cycles per beat
DEFAULT_PIPELINING_ENABLED = False   # Whether pipelining is enabled

# Drain Mode
DEFAULT_STREAMING_DRAIN = False      # False = store-and-forward, True = streaming

# SRAM Mode
DEFAULT_SRAM_MODE = "pingpong"       # "pingpong" or "monolithic"
DEFAULT_TOTAL_SRAM_SIZE = 4096       # Total SRAM per channel in bytes
DEFAULT_SRAM_SLOT_SIZE = 2048        # Slot size for ping-pong mode (bytes)

# Custom Side Constraints
DEFAULT_MAX_CUSTOM_CHANNELS = 16     # Physical slot limit on custom/user side
DEFAULT_PER_CHANNEL_CAP = 4.0        # GB/s per physical slot (limited by drain rate: 64 bytes / 16 cycles)

# ============================================================================


@dataclass
class AXIConfig:
    """
    Configuration for AXI4 performance analysis.
    
    DRAIN MODES:
    - Store-and-Forward (streaming_drain=False): 
      Entire burst must arrive before draining starts
      Time = Latency + Data_Return + Drain
      
    - Streaming (streaming_drain=True):
      Data drains as it arrives (no wait for full burst)
      Time = Latency + max(Data_Return, Drain)
      Since Drain > Data_Return: Time = Latency + Drain
    
    SRAM MODES:
    - Ping-Pong (sram_mode="pingpong"):
      2 slots of 2KB each, any read occupies entire slot
      Limits pipeline depth to 2 (only 2 bursts can be in SRAM at once)
      
    - Monolithic (sram_mode="monolithic"):
      Single 4KB SRAM, reads occupy exactly payload bytes
      Pipeline depth limited by: floor(total_sram_size / payload)
      Better for smaller payloads (e.g., 256B → 16 bursts possible!)
      
    PER-CHANNEL CONSTRAINTS:
    - Each channel can drain at: 1 beat / cycles_per_beat
    - With 64 bytes/beat and 16 cycles/beat: 4 GB/s per channel
    - With 16 channels: 16 × 4 GB/s = 64 GB/s total custom side capacity
    """
    
    # Payload and interface
    payload: int = DEFAULT_PAYLOAD
    W: int = DEFAULT_W
    f: float = DEFAULT_F
    alpha: float = DEFAULT_ALPHA
    latency: int = DEFAULT_LATENCY
    
    # Pipelining
    pipeline_depth: int = DEFAULT_PIPELINE_DEPTH
    pipelining_enabled: bool = DEFAULT_PIPELINING_ENABLED
    cycles_per_beat: int = DEFAULT_CYCLES_PER_BEAT
    
    # Drain mode
    streaming_drain: bool = DEFAULT_STREAMING_DRAIN
    
    # SRAM mode (NEW!)
    sram_mode: str = DEFAULT_SRAM_MODE  # "pingpong" or "monolithic"
    total_sram_size: int = DEFAULT_TOTAL_SRAM_SIZE
    sram_slot_size: int = DEFAULT_SRAM_SLOT_SIZE
    
    # Custom side constraints
    max_custom_channels: int = DEFAULT_MAX_CUSTOM_CHANNELS
    per_channel_cap: float = DEFAULT_PER_CHANNEL_CAP
    
    # Write-specific
    max_outstanding_bursts: Optional[int] = None
    
    def __post_init__(self):
        """Calculate derived parameters"""
        self.BL = self.payload / self.W  # Burst length in beats
        self.Bmax = self.W * self.f * self.alpha  # Peak bandwidth (GB/s)
        self.total_custom_capacity = self.max_custom_channels * self.per_channel_cap
        
        # Calculate SRAM-imposed pipeline depth limit
        if self.sram_mode == "pingpong":
            # Ping-pong: Only 2 slots, each 2KB
            # Any read occupies entire slot regardless of size
            self.max_sram_pipeline_depth = 2
        elif self.sram_mode == "monolithic":
            # Monolithic: Reads occupy exactly payload bytes
            # Max bursts = floor(total_sram_size / payload)
            self.max_sram_pipeline_depth = int(self.total_sram_size / self.payload)
        else:
            raise ValueError(f"Unknown sram_mode: {self.sram_mode}")


class AXI4Performance:
    """Performance analysis for AXI4 interfaces"""
    
    def __init__(self, config: AXIConfig):
        self.config = config
    
    def calculate_channel_bandwidth(self, num_channels: int, 
                                    pipeline_depth: Optional[int] = None) -> Dict:
        """
        Calculate bandwidth for given number of channels.
        
        Each channel is limited by:
        1. Timing (latency + data return + drain, depending on mode)
        2. Per-channel capacity (e.g., 4 GB/s drain rate limit)
        3. SRAM capacity (limits effective pipeline depth)
        
        Total bandwidth limited by:
        1. Sum of channel bandwidths
        2. Total custom side capacity (16 channels × 4 GB/s = 64 GB/s)
        3. AXI peak bandwidth
        
        SRAM Constraints:
        - Ping-pong: Max 2 bursts in SRAM at once (2 slots)
        - Monolithic: Max = floor(total_sram_size / payload) bursts
        """
        cfg = self.config
        requested_depth = pipeline_depth if pipeline_depth is not None else cfg.pipeline_depth
        
        # CRITICAL: SRAM limits effective pipeline depth
        effective_depth = min(requested_depth, cfg.max_sram_pipeline_depth)
        sram_limited = (requested_depth > cfg.max_sram_pipeline_depth)
        
        # Determine effective number of channels (limited by physical slots)
        effective_channels = min(num_channels, cfg.max_custom_channels)
        
        # Calculate per-channel bandwidth based on drain mode
        if cfg.pipelining_enabled and effective_depth > 1:
            # With pipelining: drain time can overlap with next burst fetch
            cycles_per_burst = cfg.latency + cfg.BL
        else:
            # Without pipelining: must wait for full drain
            drain_time = cfg.BL * cfg.cycles_per_beat
            
            if cfg.streaming_drain:
                # Streaming: data drains as it arrives (saves BL cycles)
                cycles_per_burst = cfg.latency + drain_time
            else:
                # Store-and-Forward: wait for all data to arrive, THEN drain
                cycles_per_burst = cfg.latency + cfg.BL + drain_time
        
        B_channel_base = (cfg.payload * cfg.f) / cycles_per_burst
        
        # Apply per-channel capacity limit (drain rate: 64 bytes / 16 cycles = 4 GB/s)
        B_channel = min(B_channel_base, cfg.per_channel_cap)
        
        # Calculate total bandwidth from channels
        total_bw_from_channels = B_channel * effective_channels
        
        # Apply system-wide limits
        total_bw = min(total_bw_from_channels, cfg.total_custom_capacity, cfg.Bmax)
        
        # Determine limiting factor
        if total_bw == cfg.Bmax:
            limited_by = "AXI_peak"
        elif total_bw == cfg.total_custom_capacity:
            limited_by = "custom_capacity"
        elif effective_channels < num_channels:
            limited_by = "max_channels"
        elif B_channel == cfg.per_channel_cap:
            limited_by = "per_channel_cap"
        else:
            limited_by = "timing"
        
        if sram_limited:
            limited_by = f"{limited_by}_SRAM_limited"
        
        # Handle write-specific outstanding burst limit
        if cfg.max_outstanding_bursts is not None:
            outstanding_per_channel = effective_depth
            max_channels_by_outstanding = cfg.max_outstanding_bursts // outstanding_per_channel
            if num_channels > max_channels_by_outstanding:
                effective_channels = max_channels_by_outstanding
                total_bw = min(B_channel * effective_channels, cfg.Bmax)
                limited_by = "outstanding_bursts"
        
        efficiency = (total_bw / cfg.Bmax) * 100
        saturated = efficiency >= 99.9
        
        return {
            'num_channels': num_channels,
            'effective_channels': effective_channels,
            'requested_pipeline_depth': requested_depth,
            'effective_pipeline_depth': effective_depth,
            'sram_limited': sram_limited,
            'B_channel': B_channel,
            'total_bw': total_bw,
            'efficiency': efficiency,
            'saturated': saturated,
            'limited_by': limited_by,
            'cycles_per_burst': cycles_per_burst,
            'drain_mode': 'streaming' if cfg.streaming_drain else 'store_and_forward',
            'sram_mode': cfg.sram_mode
        }
    
    def generate_performance_table(self, max_channels: int = MAX_CHANNELS,
                                   pipeline_depth: Optional[int] = None) -> pd.DataFrame:
        """Generate performance table for range of channel counts"""
        results = []
        
        for n in range(1, max_channels + 1):
            perf = self.calculate_channel_bandwidth(n, pipeline_depth)
            
            row = {
                'Channels': perf['num_channels'],
                'Effective_Channels': perf['effective_channels'],
                'Requested_Pipeline': perf['requested_pipeline_depth'],
                'Effective_Pipeline': perf['effective_pipeline_depth'],
                'SRAM_Limited': perf['sram_limited'],
                'BW_per_Channel_GBps': perf['B_channel'],
                'Total_BW_GBps': perf['total_bw'],
                'Efficiency_%': perf['efficiency'],
                'Saturated': perf['saturated'],
                'Limited_By': perf['limited_by'],
                'Cycles_per_Burst': perf['cycles_per_burst'],
                'Drain_Mode': perf['drain_mode'],
                'SRAM_Mode': perf['sram_mode']
            }
            
            # Add outstanding bursts info if applicable
            if self.config.max_outstanding_bursts is not None:
                row['Outstanding_Bursts'] = perf['effective_channels'] * perf['effective_pipeline_depth']
            
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
            # Recalculate SRAM limit
            self.config.__post_init__()
            results[payload] = self.generate_performance_table(max_channels)
        
        # Restore original
        self.config.payload = original_payload
        self.config.BL = original_BL
        self.config.__post_init__()
        
        return results
    
    def find_saturation_point(self, max_channels: int = MAX_CHANNELS) -> Dict:
        """Find minimum channels needed to saturate bandwidth"""
        for n in range(1, max_channels + 1):
            perf = self.calculate_channel_bandwidth(n)
            if perf['saturated']:
                return {
                    'channels': n,
                    'bandwidth': perf['total_bw'],
                    'efficiency': perf['efficiency'],
                    'limited_by': perf['limited_by']
                }
        
        return {
            'channels': None,
            'bandwidth': None,
            'efficiency': None,
            'message': f'Cannot saturate within {max_channels} channels'
        }


@dataclass
class MixedAXIConfig:
    """Configuration for mixed read/write analysis"""
    
    read_config: AXIConfig
    write_config: AXIConfig
    read_fraction: float = 0.5
    
    def __post_init__(self):
        """Validate configurations"""
        assert 0 <= self.read_fraction <= 1, "read_fraction must be between 0 and 1"
        assert self.read_config.Bmax == self.write_config.Bmax, \
            "Read and write configs must have same peak bandwidth"


class MixedAXI4Performance:
    """Performance analysis for mixed read/write workloads"""
    
    def __init__(self, config: MixedAXIConfig):
        self.config = config
        self.read_perf = AXI4Performance(config.read_config)
        self.write_perf = AXI4Performance(config.write_config)
    
    def calculate_mixed_bandwidth(self, num_channels: int) -> Dict:
        """Calculate bandwidth for mixed read/write with given split"""
        cfg = self.config
        
        read_channels = int(num_channels * cfg.read_fraction)
        write_channels = num_channels - read_channels
        
        if read_channels == 0:
            read_bw = 0
            read_eff = 0
        else:
            read_result = self.read_perf.calculate_channel_bandwidth(read_channels)
            read_bw = read_result['total_bw']
            read_eff = read_result['efficiency']
        
        if write_channels == 0:
            write_bw = 0
            write_eff = 0
        else:
            write_result = self.write_perf.calculate_channel_bandwidth(write_channels)
            write_bw = write_result['total_bw']
            write_eff = write_result['efficiency']
        
        combined_bw = read_bw + write_bw
        combined_eff = (combined_bw / cfg.read_config.Bmax) * 100
        
        return {
            'num_channels': num_channels,
            'read_channels': read_channels,
            'write_channels': write_channels,
            'read_bw': read_bw,
            'write_bw': write_bw,
            'combined_bw': combined_bw,
            'read_efficiency': read_eff,
            'write_efficiency': write_eff,
            'combined_efficiency': combined_eff
        }
    
    def generate_mixed_table(self, max_channels: int = MAX_CHANNELS) -> pd.DataFrame:
        """Generate performance table for mixed workload"""
        results = []
        
        for n in range(1, max_channels + 1):
            perf = self.calculate_mixed_bandwidth(n)
            results.append({
                'Channels': perf['num_channels'],
                'Read_Channels': perf['read_channels'],
                'Write_Channels': perf['write_channels'],
                'Read_BW_GBps': perf['read_bw'],
                'Write_BW_GBps': perf['write_bw'],
                'Combined_BW_GBps': perf['combined_bw'],
                'Efficiency_%': perf['combined_efficiency']
            })
        
        return pd.DataFrame(results)


def show_defaults():
    """Print current default configuration values"""
    print("="*70)
    print("  PYPERF DEFAULT CONFIGURATION")
    print("="*70)
    print(f"\n  Max Channels:        {MAX_CHANNELS}")
    print(f"\n  AXI Interface:")
    print(f"    Width (W):         {DEFAULT_W} bytes/beat")
    print(f"    Frequency (f):     {DEFAULT_F} GHz")
    print(f"    Payload Options:   {DEFAULT_PAYLOAD_OPTIONS} bytes")
    print(f"    Default Payload:   {DEFAULT_PAYLOAD} bytes")
    print(f"    Alpha:             {DEFAULT_ALPHA}")
    print(f"    Latency:           {DEFAULT_LATENCY} cycles")
    print(f"\n  Pipelining:")
    print(f"    Pipeline Depth:    {DEFAULT_PIPELINE_DEPTH}")
    print(f"    Cycles per Beat:   {DEFAULT_CYCLES_PER_BEAT}")
    print(f"\n  Drain Mode:")
    drain_mode_str = "Streaming" if DEFAULT_STREAMING_DRAIN else "Store-and-Forward"
    print(f"    Mode:              {drain_mode_str}")
    print(f"    Store-and-Forward: Entire burst arrives, then drains")
    print(f"    Streaming:         Data drains as it arrives (saves BL cycles)")
    print(f"\n  SRAM Mode:")
    print(f"    Mode:              {DEFAULT_SRAM_MODE}")
    print(f"    Total Size:        {DEFAULT_TOTAL_SRAM_SIZE} bytes per channel")
    if DEFAULT_SRAM_MODE == "pingpong":
        print(f"    Slot Size:         {DEFAULT_SRAM_SLOT_SIZE} bytes (2 slots)")
        print(f"    Max Pipeline:      2 (limited by 2 slots)")
    else:
        print(f"    Max Pipeline:      Depends on payload (4096/payload)")
    print(f"\n  Custom Side Constraints:")
    print(f"    Max Channels:      {DEFAULT_MAX_CUSTOM_CHANNELS} physical slots")
    print(f"    Per-Channel Cap:   {DEFAULT_PER_CHANNEL_CAP} GB/s per slot")
    print(f"    Total Capacity:    {DEFAULT_MAX_CUSTOM_CHANNELS * DEFAULT_PER_CHANNEL_CAP} GB/s")
    print(f"\n  Drain Rate Analysis:")
    drain_rate = DEFAULT_W / DEFAULT_CYCLES_PER_BEAT * DEFAULT_F
    print(f"    Per-Channel Drain: {drain_rate:.2f} GB/s (= {DEFAULT_W} bytes / {DEFAULT_CYCLES_PER_BEAT} cycles)")
    print(f"    Max Total Drain:   {drain_rate * DEFAULT_MAX_CUSTOM_CHANNELS:.2f} GB/s ({DEFAULT_MAX_CUSTOM_CHANNELS} channels)")
    print("="*70)
    print("\nTo change these values, edit the constants at the top of performance.py")
    print("="*70 + "\n")
