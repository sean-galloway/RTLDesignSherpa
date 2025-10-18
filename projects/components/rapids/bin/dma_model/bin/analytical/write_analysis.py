# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: write_analysis
# Purpose: Analytical Model for AXI4 Write Path
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Analytical Model for AXI4 Write Path

This module provides analytical performance modeling for the write path,
complementing the read path analysis in current_design.py.

Write path characteristics:
- Smaller bursts: 256 bytes (4 beats @ 64 bytes/beat)
- Outstanding burst limit: 32 system-wide (enables pipelining)
- Different bottlenecks: outstanding limit allows overlap
- Fill from custom side + write to memory

IMPORTANT: Write path is analyzed SEPARATELY from read path.
They share AXI bandwidth but are independent operations.

Usage:
    from analytical.write_analysis import get_write_performance
    
    results = get_write_performance(num_channels=16, verbose=True)
"""

import sys
import os
import pandas as pd
import numpy as np

# Add pyperf to path if needed
try:
    from pyperf import AXIConfig, AXI4Performance
    from pyperf import DEFAULT_W, DEFAULT_F, DEFAULT_ALPHA, DEFAULT_LATENCY
except ImportError:
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
    from pyperf import AXIConfig, AXI4Performance
    from pyperf import DEFAULT_W, DEFAULT_F, DEFAULT_ALPHA, DEFAULT_LATENCY


def calculate_write_bandwidth(payload: int,
                              num_channels: int,
                              max_outstanding: int,
                              bus_width: int = DEFAULT_W,
                              frequency: float = DEFAULT_F,
                              alpha: float = DEFAULT_ALPHA,
                              latency: int = DEFAULT_LATENCY) -> dict:
    """
    Calculate write bandwidth with proper outstanding burst accounting.
    
    Key insight: Outstanding bursts enable pipelining!
    - Multiple writes can be in flight simultaneously
    - Effective throughput >> single burst calculation
    - Limited by: min(outstanding_capacity, AXI_peak, fill_rate)
    
    Args:
        payload: Write burst size in bytes
        num_channels: Number of write channels
        max_outstanding: System-wide outstanding burst limit
        bus_width: AXI bus width in bytes
        frequency: Clock frequency in GHz
        alpha: Protocol efficiency
        latency: Memory latency in cycles
    
    Returns:
        Dictionary with bandwidth calculations
    """
    # Basic parameters
    burst_length = payload / bus_width  # beats
    axi_peak_bw = bus_width * frequency * alpha  # GB/s
    
    # Timing for single burst (no pipelining)
    data_send_cycles = burst_length  # 1 beat per cycle
    total_cycles_single = latency + data_send_cycles
    single_burst_bw = (payload * frequency) / total_cycles_single
    
    # Outstanding bursts per channel
    outstanding_per_channel = max_outstanding / num_channels
    
    # With pipelining from outstanding bursts:
    # Once pipeline is full, we send one burst every data_send_cycles
    # (latency is hidden by other outstanding bursts)
    if outstanding_per_channel >= 2:
        # Can pipeline - limited by data send rate
        effective_cycles = data_send_cycles
    else:
        # Cannot pipeline effectively - must wait for latency
        effective_cycles = total_cycles_single
    
    # Per-channel pipelined bandwidth
    channel_bw_pipelined = (payload * frequency) / effective_cycles
    
    # Total bandwidth (sum across channels, limited by AXI peak)
    total_bw_unlimited = channel_bw_pipelined * num_channels
    total_bw = min(total_bw_unlimited, axi_peak_bw)
    
    # Determine limiting factor
    if total_bw >= axi_peak_bw * 0.99:
        limited_by = "AXI_peak"
    elif outstanding_per_channel < 2:
        limited_by = "outstanding_bursts"
    else:
        limited_by = "data_send_rate"
    
    return {
        'payload': payload,
        'num_channels': num_channels,
        'burst_length': burst_length,
        'max_outstanding': max_outstanding,
        'outstanding_per_channel': outstanding_per_channel,
        'latency_cycles': latency,
        'data_send_cycles': data_send_cycles,
        'total_cycles_single': total_cycles_single,
        'single_burst_bw': single_burst_bw,
        'channel_bw_pipelined': channel_bw_pipelined,
        'total_bw': total_bw,
        'axi_peak_bw': axi_peak_bw,
        'efficiency_pct': (total_bw / axi_peak_bw) * 100,
        'limited_by': limited_by,
        'can_pipeline': outstanding_per_channel >= 2
    }


def get_write_performance(num_channels: int = 16,
                         payload: int = 256,
                         max_outstanding: int = 32,
                         verbose: bool = False):
    """
    Get baseline write path performance.
    
    Args:
        num_channels: Number of write channels
        payload: Write burst size in bytes (default: 256)
        max_outstanding: System-wide outstanding burst limit
        verbose: Print detailed results
    
    Returns:
        Dictionary with write performance data
    """
    result = calculate_write_bandwidth(
        payload=payload,
        num_channels=num_channels,
        max_outstanding=max_outstanding
    )
    
    if verbose:
        print("="*80)
        print("  WRITE PATH PERFORMANCE (Analytical)")
        print("="*80)
        print(f"\nConfiguration:")
        print(f"  Payload:              {payload} bytes (write burst)")
        print(f"  Burst Length:         {result['burst_length']:.0f} beats")
        print(f"  Channels:             {num_channels}")
        print(f"  Max Outstanding:      {max_outstanding} (system-wide)")
        print(f"  Outstanding/channel:  {result['outstanding_per_channel']:.1f}")
        print(f"  Peak BW (AXI):        {result['axi_peak_bw']:.2f} GB/s")
        
        print(f"\nWrite Timing:")
        print(f"  Memory latency:       {result['latency_cycles']} cycles")
        print(f"  Data send:            {result['data_send_cycles']:.0f} cycles")
        print(f"  Total (no pipeline):  {result['total_cycles_single']:.0f} cycles")
        
        print(f"\nSingle Burst Performance (no pipelining):")
        print(f"  Bandwidth:            {result['single_burst_bw']:.3f} GB/s")
        
        print(f"\nPipelined Performance (with outstanding bursts):")
        print(f"  Can pipeline:         {'YES' if result['can_pipeline'] else 'NO'}")
        print(f"  Channel BW:           {result['channel_bw_pipelined']:.3f} GB/s")
        print(f"  Total BW:             {result['total_bw']:.3f} GB/s")
        print(f"  Limited by:           {result['limited_by']}")
        print(f"  Efficiency:           {result['efficiency_pct']:.1f}% of AXI peak")
        
        print("\nKey Insight:")
        if result['can_pipeline']:
            improvement = ((result['channel_bw_pipelined'] / result['single_burst_bw']) - 1) * 100
            print(f"  Outstanding bursts enable pipelining: +{improvement:.0f}% improvement")
        else:
            print(f"  Insufficient outstanding bursts per channel for effective pipelining")
        
        print("="*80 + "\n")
    
    return result


def get_optimized_write_performance(num_channels: int = 16,
                                   payload: int = 256,
                                   max_outstanding: int = 64,
                                   verbose: bool = False):
    """
    Get optimized write path performance (increased outstanding limit).
    
    Args:
        num_channels: Number of write channels
        payload: Write burst size in bytes
        max_outstanding: Increased outstanding burst limit
        verbose: Print detailed results
    
    Returns:
        Dictionary with optimized write performance data
    """
    result = calculate_write_bandwidth(
        payload=payload,
        num_channels=num_channels,
        max_outstanding=max_outstanding
    )
    
    if verbose:
        print("="*80)
        print("  OPTIMIZED WRITE PATH PERFORMANCE")
        print("="*80)
        print(f"\nConfiguration:")
        print(f"  Payload:              {payload} bytes")
        print(f"  Channels:             {num_channels}")
        print(f"  Max Outstanding:      {max_outstanding} (increased from 32)")
        print(f"  Outstanding/channel:  {result['outstanding_per_channel']:.1f}")
        
        print(f"\nPipelined Performance:")
        print(f"  Total BW:             {result['total_bw']:.3f} GB/s")
        print(f"  Limited by:           {result['limited_by']}")
        print(f"  Efficiency:           {result['efficiency_pct']:.1f}%")
        print("="*80 + "\n")
    
    return result


def compare_write_payloads(payloads: list = None,
                          num_channels: int = 16,
                          max_outstanding: int = 32,
                          verbose: bool = False):
    """
    Compare write performance across different payload sizes.
    
    Args:
        payloads: List of payload sizes (default: [128, 256, 512, 1024])
        num_channels: Number of channels
        max_outstanding: Outstanding burst limit
        verbose: Print comparison
    
    Returns:
        Dictionary with results for each payload
    """
    if payloads is None:
        payloads = [128, 256, 512, 1024]
    
    results = {}
    
    if verbose:
        print("="*80)
        print("  WRITE PATH: PAYLOAD SIZE COMPARISON")
        print("="*80)
        print(f"\nChannels: {num_channels}, Outstanding limit: {max_outstanding}\n")
        print(f"{'Payload':<12} {'Burst':<10} {'Single':<12} {'Pipelined':<12} {f'{num_channels} Ch':<12}")
        print(f"{'':12} {'Beats':<10} {'GB/s':<12} {'GB/s':<12} {'Total GB/s':<12}")
        print("-" * 80)
    
    for payload in payloads:
        result = calculate_write_bandwidth(
            payload=payload,
            num_channels=num_channels,
            max_outstanding=max_outstanding
        )
        
        results[payload] = result
        
        if verbose:
            print(f"{payload:4d}B       {result['burst_length']:2.0f}       "
                  f"{result['single_burst_bw']:5.3f}       "
                  f"{result['channel_bw_pipelined']:5.3f}       "
                  f"{result['total_bw']:6.2f}")
    
    if verbose:
        print("\nKey Insights:")
        print("  - Outstanding bursts enable write pipelining")
        print("  - Larger payloads have longer data send time")
        print("  - Total bandwidth limited by AXI peak (57.6 GB/s)")
        print("="*80 + "\n")
    
    return results


if __name__ == "__main__":
    print("\n" + "="*80)
    print("  WRITE PATH PERFORMANCE ANALYSIS")
    print("  (Analyzed separately from read path)")
    print("="*80 + "\n")
    
    # 1. Baseline write performance
    print("1. BASELINE WRITE PERFORMANCE")
    print("-" * 80)
    baseline_write = get_write_performance(
        num_channels=16,
        payload=256,
        max_outstanding=32,
        verbose=True
    )
    
    # 2. Write payload comparison
    print("\n2. WRITE PAYLOAD COMPARISON")
    print("-" * 80)
    payload_comparison = compare_write_payloads(
        payloads=[128, 256, 512, 1024],
        num_channels=16,
        max_outstanding=32,
        verbose=True
    )
    
    # 3. Optimized write (increased outstanding limit)
    print("\n3. OPTIMIZED WRITE (Increased Outstanding)")
    print("-" * 80)
    optimized_write = get_optimized_write_performance(
        num_channels=16,
        payload=256,
        max_outstanding=64,
        verbose=True
    )
    
    # 4. Comparison
    print("\n4. BASELINE VS OPTIMIZED COMPARISON")
    print("-" * 80)
    improvement = ((optimized_write['total_bw'] / baseline_write['total_bw']) - 1) * 100
    print(f"\nBaseline:    {baseline_write['total_bw']:.2f} GB/s")
    print(f"Optimized:   {optimized_write['total_bw']:.2f} GB/s")
    print(f"Improvement: +{improvement:.1f}%")
    print("\n" + "="*80)
    
    print("\nIMPORTANT NOTE:")
    print("  Write and read paths share the same AXI interface (57.6 GB/s peak).")
    print("  They are analyzed separately; actual combined throughput depends")
    print("  on workload mix and AXI arbitration.")
    print("="*80 + "\n")
