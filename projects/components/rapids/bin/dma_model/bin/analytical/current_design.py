# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: current_design
# Purpose: Analytical Model for Current AXI4 Design
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Analytical Model for Current AXI4 Design

This script provides the analytical performance model from current_design.ipynb
in a runnable format that can be imported or executed standalone.

Usage:
    python current_design.py              # Run full analysis
    from current_design import get_baseline_performance  # Import specific functions
"""

import sys
import pandas as pd
import numpy as np

# Add pyperf to path if running standalone
try:
    from pyperf import (
        AXIConfig, AXI4Performance, PerformanceGraphs,
        DEFAULT_PAYLOAD_OPTIONS, show_defaults
    )
except ImportError:
    import os
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
    from pyperf import (
        AXIConfig, AXI4Performance, PerformanceGraphs,
        DEFAULT_PAYLOAD_OPTIONS, show_defaults
    )


def get_baseline_performance(verbose=False):
    """
    Get baseline (current design) read performance.
    
    Returns:
        dict: Contains config, performance object, and results dataframe
    """
    # Configure baseline read performance
    config = AXIConfig(
        payload=2048,           # 2KB bursts
        pipeline_depth=1,       # No pipelining - stop and wait
        pipelining_enabled=False,
        max_custom_channels=16, # Hardware limit: 16 physical slots
        per_channel_cap=4.0,    # Each slot limited to 4 GB/s by drain rate
        cycles_per_beat=16,     # Drain rate: 1 beat every 16 cycles
        streaming_drain=False,  # Store-and-Forward (current design)
        sram_mode="pingpong"    # Ping-pong SRAM (2 slots of 2KB)
    )
    
    perf = AXI4Performance(config)
    df = perf.generate_performance_table(max_channels=32)
    
    if verbose:
        print("="*80)
        print("  BASELINE READ PERFORMANCE (Current Design)")
        print("="*80)
        print("\nConfiguration:")
        print(f"  Payload:            {config.payload} bytes (2KB)")
        print(f"  Burst Length:       {config.BL:.0f} beats")
        print(f"  Pipeline:           {config.pipeline_depth} (stop-and-wait)")
        print(f"  Drain Mode:         Store-and-Forward")
        print(f"  SRAM Mode:          Ping-Pong (2 slots × 2KB)")
        print(f"  Max Custom Slots:   {config.max_custom_channels}")
        print(f"  Per-Slot Cap:       {config.per_channel_cap} GB/s")
        print(f"  Total Custom Cap:   {config.total_custom_capacity} GB/s")
        print(f"  Peak BW (AXI):      {config.Bmax:.2f} GB/s")
        
        # Timing breakdown
        single = perf.calculate_channel_bandwidth(1)
        print(f"\nTiming Breakdown (per read burst):")
        print(f"  Latency:            {config.latency} cycles")
        print(f"  Data Return:        {config.BL:.0f} cycles")
        print(f"  Drain Time:         {config.BL * config.cycles_per_beat:.0f} cycles")
        print(f"  TOTAL:              {single['cycles_per_burst']:.0f} cycles")
        
        print(f"\nSingle Channel Performance (Read):")
        print(f"  Bandwidth:          {single['B_channel']:.3f} GB/s")
        print(f"  Limited by:         {single['limited_by']}")
        
        multi = perf.calculate_channel_bandwidth(16)
        print(f"\n16 Channel Performance (Read):")
        print(f"  Total Bandwidth:    {multi['total_bw']:.3f} GB/s")
        print(f"  Limited by:         {multi['limited_by']}")
        print(f"  Efficiency:         {multi['efficiency']:.1f}% of AXI peak")
        print("="*80 + "\n")
    
    return {
        'config': config,
        'performance': perf,
        'dataframe': df
    }


def compare_all_payloads(verbose=False):
    """
    Compare performance across all payload sizes.
    
    Returns:
        dict: Results for each payload size
    """
    base_config = AXIConfig(
        pipeline_depth=1,
        pipelining_enabled=False,
        max_custom_channels=16,
        per_channel_cap=4.0,
        cycles_per_beat=16,
        streaming_drain=False,
        sram_mode="pingpong"
    )
    
    perf = AXI4Performance(base_config)
    results = perf.compare_payloads(max_channels=32)
    
    if verbose:
        print("="*80)
        print("  PAYLOAD SIZE COMPARISON (All Store-and-Forward, No Pipeline)")
        print("  READ PATH ANALYSIS")
        print("="*80)
        print(f"\n{'Payload':<12} {'Burst':<10} {'Drain':<12} {'Total':<12} {'Single':<10} {'16 Ch':<10}")
        print(f"{'':12} {'Beats':<10} {'Cycles':<12} {'Cycles':<12} {'Read GB/s':<10} {'Read GB/s':<10}")
        print("-" * 80)
        
        for payload in DEFAULT_PAYLOAD_OPTIONS:
            df = results[payload]
            single_bw = df.iloc[0]['BW_per_Channel_GBps']
            multi_bw = df[df['Channels'] == 16].iloc[0]['Total_BW_GBps']
            burst_len = payload / base_config.W
            drain_cycles = burst_len * base_config.cycles_per_beat
            total_cycles = base_config.latency + burst_len + drain_cycles
            
            marker = " ← Current" if payload == 2048 else ""
            print(f"{payload:4d}B       {burst_len:2.0f}       {drain_cycles:5.0f}       "
                  f"{total_cycles:5.0f}       {single_bw:5.3f}     {multi_bw:6.2f}{marker}")
        
        print("\nKey Insight:")
        print("  - Larger payloads have longer drain times")
        print("  - With 16 channels, all approach ~4 GB/s per-channel limit")
        print("  - Total bandwidth limited by custom capacity (64 GB/s)")
        print("="*80 + "\n")
    
    return results


def analyze_pipelining_impact(payload=2048, max_depth=10, verbose=False):
    """
    Analyze impact of pipelining for a given payload size.
    
    Args:
        payload: Burst size in bytes
        max_depth: Maximum pipeline depth to test
        verbose: Print detailed results
    
    Returns:
        dict: Results for each pipeline depth
    """
    results = {}
    
    # Baseline: no pipelining
    config_baseline = AXIConfig(
        payload=payload,
        pipeline_depth=1,
        pipelining_enabled=False,
        max_custom_channels=16,
        per_channel_cap=4.0,
        cycles_per_beat=16,
        streaming_drain=False,
        sram_mode="pingpong"
    )
    
    perf_baseline = AXI4Performance(config_baseline)
    results[1] = {
        'config': config_baseline,
        'performance': perf_baseline,
        'dataframe': perf_baseline.generate_performance_table(max_channels=32)
    }
    
    # Test various pipeline depths
    for depth in range(2, max_depth + 1):
        config = AXIConfig(
            payload=payload,
            pipeline_depth=depth,
            pipelining_enabled=True,
            max_custom_channels=16,
            per_channel_cap=4.0,
            cycles_per_beat=16,
            streaming_drain=False,
            sram_mode="pingpong"
        )
        
        perf = AXI4Performance(config)
        results[depth] = {
            'config': config,
            'performance': perf,
            'dataframe': perf.generate_performance_table(max_channels=32)
        }
        
        # Check if we've saturated
        single = perf.calculate_channel_bandwidth(1)
        if single['B_channel'] >= 3.96:  # 99% of 4 GB/s
            break
    
    if verbose:
        print("="*80)
        print(f"  PIPELINING IMPACT: {payload} byte payload")
        print("  READ PATH ANALYSIS")
        print("="*80)
        print(f"\n{'Depth':<10} {'Single Ch':<12} {'16 Ch':<12} {'Improvement':<15}")
        print(f"{'':10} {'Read GB/s':<12} {'Read GB/s':<12} {'vs Baseline':<15}")
        print("-" * 60)
        
        baseline_single = results[1]['performance'].calculate_channel_bandwidth(1)['B_channel']
        baseline_multi = results[1]['dataframe'][results[1]['dataframe']['Channels'] == 16].iloc[0]['Total_BW_GBps']
        
        for depth in sorted(results.keys()):
            perf = results[depth]['performance']
            df = results[depth]['dataframe']
            
            single = perf.calculate_channel_bandwidth(1)
            single_bw = single['B_channel']
            multi_bw = df[df['Channels'] == 16].iloc[0]['Total_BW_GBps']
            
            improvement = ((single_bw / baseline_single) - 1) * 100
            
            if depth == 1:
                print(f"{depth:<10} {single_bw:6.3f}      {multi_bw:6.2f}      baseline")
            else:
                saturated = " ✓" if single_bw >= 3.96 else ""
                print(f"{depth:<10} {single_bw:6.3f}      {multi_bw:6.2f}      +{improvement:5.1f}%{saturated}")
        
        print("\nKey Insight:")
        print("  - Pipelining allows drain to overlap with next fetch")
        print("  - Depth=2-4 sufficient to reach 4 GB/s per-channel cap")
        print("  - Total bandwidth improves from ~44 GB/s to ~64 GB/s")
        print("="*80 + "\n")
    
    return results


def compare_drain_modes(payload=2048, verbose=False):
    """
    Compare Store-and-Forward vs Streaming drain modes.
    
    Args:
        payload: Burst size in bytes
        verbose: Print detailed results
    
    Returns:
        dict: Results for both drain modes
    """
    # Store-and-Forward (current)
    config_sf = AXIConfig(
        payload=payload,
        pipeline_depth=1,
        pipelining_enabled=False,
        max_custom_channels=16,
        per_channel_cap=4.0,
        cycles_per_beat=16,
        streaming_drain=False,
        sram_mode="pingpong"
    )
    
    # Streaming (improved)
    config_streaming = AXIConfig(
        payload=payload,
        pipeline_depth=1,
        pipelining_enabled=False,
        max_custom_channels=16,
        per_channel_cap=4.0,
        cycles_per_beat=16,
        streaming_drain=True,
        sram_mode="pingpong"
    )
    
    perf_sf = AXI4Performance(config_sf)
    perf_streaming = AXI4Performance(config_streaming)
    
    results = {
        'store_and_forward': {
            'config': config_sf,
            'performance': perf_sf,
            'dataframe': perf_sf.generate_performance_table(max_channels=32)
        },
        'streaming': {
            'config': config_streaming,
            'performance': perf_streaming,
            'dataframe': perf_streaming.generate_performance_table(max_channels=32)
        }
    }
    
    if verbose:
        single_sf = perf_sf.calculate_channel_bandwidth(1)
        single_streaming = perf_streaming.calculate_channel_bandwidth(1)
        
        df_sf = results['store_and_forward']['dataframe']
        df_streaming = results['streaming']['dataframe']
        
        multi_sf = df_sf[df_sf['Channels'] == 16].iloc[0]['Total_BW_GBps']
        multi_streaming = df_streaming[df_streaming['Channels'] == 16].iloc[0]['Total_BW_GBps']
        
        improvement = ((single_streaming['B_channel'] / single_sf['B_channel']) - 1) * 100
        
        print("="*80)
        print(f"  DRAIN MODE COMPARISON: {payload} byte payload")
        print("  READ PATH ANALYSIS")
        print("="*80)
        print(f"\n{'Mode':<20} {'Single Ch':<12} {'16 Ch':<12} {'Timing':<15}")
        print(f"{'':20} {'Read GB/s':<12} {'Read GB/s':<12} {'cycles':<15}")
        print("-" * 70)
        print(f"{'Store-and-Forward':<20} {single_sf['B_channel']:6.3f}      "
              f"{multi_sf:6.2f}      {single_sf['cycles_per_burst']:.0f}")
        print(f"{'Streaming':<20} {single_streaming['B_channel']:6.3f}      "
              f"{multi_streaming:6.2f}      {single_streaming['cycles_per_burst']:.0f}  "
              f"(+{improvement:.1f}%)")
        
        print("\nKey Insight:")
        print("  - Streaming eliminates data return wait time")
        burst_len = payload / config_sf.W
        print(f"  - Saves {burst_len:.0f} cycles (burst length)")
        print(f"  - Improvement: ~{improvement:.1f}% for single channel")
        print("  - But still limited by drain rate (4 GB/s)")
        print("="*80 + "\n")
    
    return results


def get_optimized_performance(pipeline_depth=4, streaming=True, monolithic=False, 
                              payload=2048, verbose=False):
    """
    Get optimized design performance.
    
    Args:
        pipeline_depth: Pipeline depth to use
        streaming: Use streaming drain instead of store-and-forward
        monolithic: Use monolithic SRAM instead of ping-pong
        payload: Burst size in bytes
        verbose: Print detailed results
    
    Returns:
        dict: Contains config, performance object, and results dataframe
    """
    sram_mode = "monolithic" if monolithic else "pingpong"
    
    config = AXIConfig(
        payload=payload,
        pipeline_depth=pipeline_depth,
        pipelining_enabled=(pipeline_depth > 1),
        max_custom_channels=16,
        per_channel_cap=4.0,
        cycles_per_beat=16,
        streaming_drain=streaming,
        sram_mode=sram_mode
    )
    
    perf = AXI4Performance(config)
    df = perf.generate_performance_table(max_channels=32)
    
    if verbose:
        print("="*80)
        print("  OPTIMIZED READ PERFORMANCE")
        print("="*80)
        print("\nConfiguration:")
        print(f"  Payload:            {config.payload} bytes")
        print(f"  Pipeline Depth:     {config.pipeline_depth}")
        print(f"  Drain Mode:         {'Streaming' if streaming else 'Store-and-Forward'}")
        print(f"  SRAM Mode:          {sram_mode.title()}")
        print(f"  SRAM Limit:         {config.max_sram_pipeline_depth} bursts")
        
        single = perf.calculate_channel_bandwidth(1)
        print(f"\nSingle Channel Performance (Read):")
        print(f"  Bandwidth:          {single['B_channel']:.3f} GB/s")
        print(f"  Cycles per burst:   {single['cycles_per_burst']:.0f}")
        print(f"  Limited by:         {single['limited_by']}")
        
        multi = perf.calculate_channel_bandwidth(16)
        print(f"\n16 Channel Performance (Read):")
        print(f"  Total Bandwidth:    {multi['total_bw']:.3f} GB/s")
        print(f"  Efficiency:         {multi['efficiency']:.1f}% of AXI peak")
        
        # Compare to baseline
        baseline = get_baseline_performance(verbose=False)
        baseline_multi = baseline['performance'].calculate_channel_bandwidth(16)
        improvement = ((multi['total_bw'] / baseline_multi['total_bw']) - 1) * 100
        
        print(f"\nImprovement vs Baseline:")
        print(f"  Baseline:           {baseline_multi['total_bw']:.2f} GB/s (read)")
        print(f"  Optimized:          {multi['total_bw']:.2f} GB/s (read)")
        print(f"  Gain:               +{improvement:.1f}%")
        
        target_met = "✓ YES" if multi['total_bw'] >= 50 else "✗ NO"
        print(f"  Meets 50+ GB/s:     {target_met}")
        print("="*80 + "\n")
    
    return {
        'config': config,
        'performance': perf,
        'dataframe': df
    }


def run_full_analysis():
    """Run complete analysis with visualizations."""
    print("\n" + "="*80)
    print("  AXI4 READ PERFORMANCE ANALYSIS")
    print("  Current Design (Baseline) + Optimizations")
    print("="*80 + "\n")
    
    # 1. Baseline performance
    print("1. BASELINE PERFORMANCE - READ PATH")
    print("-" * 80)
    baseline = get_baseline_performance(verbose=True)
    
    # 2. Payload comparison
    print("\n2. PAYLOAD SIZE COMPARISON")
    print("-" * 80)
    payload_results = compare_all_payloads(verbose=True)
    
    # 3. Pipelining impact
    print("\n3. PIPELINING IMPACT (2KB payload)")
    print("-" * 80)
    pipeline_results = analyze_pipelining_impact(payload=2048, max_depth=10, verbose=True)
    
    # 4. Drain mode comparison
    print("\n4. DRAIN MODE COMPARISON (2KB payload)")
    print("-" * 80)
    drain_results = compare_drain_modes(payload=2048, verbose=True)
    
    # 5. Fully optimized
    print("\n5. FULLY OPTIMIZED DESIGN")
    print("-" * 80)
    optimized = get_optimized_performance(
        pipeline_depth=4, 
        streaming=True, 
        monolithic=False,  # For 2KB, ping-pong and monolithic are same
        payload=2048, 
        verbose=True
    )
    
    print("\n" + "="*80)
    print("  SUMMARY - READ PATH")
    print("="*80)
    
    baseline_bw = baseline['performance'].calculate_channel_bandwidth(16)['total_bw']
    optimized_bw = optimized['performance'].calculate_channel_bandwidth(16)['total_bw']
    total_improvement = ((optimized_bw / baseline_bw) - 1) * 100
    
    print(f"\nBaseline (Current):   {baseline_bw:.2f} GB/s @ 16 channels (read)")
    print(f"Optimized (Best):     {optimized_bw:.2f} GB/s @ 16 channels (read)")
    print(f"Total Improvement:    +{total_improvement:.1f}%")
    print(f"\nTarget (50+ GB/s):    {'✓ MET' if optimized_bw >= 50 else '✗ NOT MET'}")
    print("\n" + "="*80 + "\n")
    
    return {
        'baseline': baseline,
        'payload_comparison': payload_results,
        'pipelining': pipeline_results,
        'drain_modes': drain_results,
        'optimized': optimized
    }


if __name__ == "__main__":
    # Run full analysis when executed as script
    results = run_full_analysis()
    
    # Optionally generate plots
    try:
        import matplotlib.pyplot as plt
        from pyperf import PerformanceGraphs
        
        print("\nGenerating visualization plots...")
        graphs = PerformanceGraphs()
        
        # Plot baseline
        baseline_df = results['baseline']['dataframe']
        baseline_config = results['baseline']['config']
        graphs.plot_combined(
            baseline_df, 
            baseline_config.Bmax,
            title="Baseline Performance (Current Design)",
            show=True
        )
        
        # Plot optimized
        optimized_df = results['optimized']['dataframe']
        optimized_config = results['optimized']['config']
        graphs.plot_combined(
            optimized_df,
            optimized_config.Bmax,
            title="Optimized Performance (Pipeline + Streaming)",
            show=True
        )
        
        # Compare baseline vs optimized
        graphs.plot_comparison(
            [baseline_df, optimized_df],
            ['Baseline (No Pipeline)', 'Optimized (Pipeline=4, Streaming)'],
            baseline_config.Bmax,
            title="Baseline vs Optimized Comparison",
            show=True
        )
        
    except ImportError:
        print("\nMatplotlib not available. Skipping plots.")
    except Exception as e:
        print(f"\nError generating plots: {e}")
