#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: run_payload_sweep
# Purpose: Payload Size Sweep Analysis
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Payload Size Sweep Analysis

This script runs performance analysis across different payload sizes (256B, 512B, 1KB, 2KB)
to show how SRAM mode and optimizations affect performance for different burst sizes.

Key insight: Smaller payloads benefit MASSIVELY from monolithic SRAM!
"""

import sys
import os
from typing import Dict, List
import pandas as pd

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from pyperf import AXIConfig, AXI4Performance
from simpy_model.current_design import run_baseline_simulation, run_optimized_simulation


def run_analytical_payload_sweep(payloads: List[int] = [256, 512, 1024, 2048],
                                 num_channels: int = 16) -> pd.DataFrame:
    """
    Run analytical model across different payload sizes.

    For each payload, test:
    - Baseline (no pipeline, store-and-forward, ping-pong)
    - Optimized (pipeline=4, streaming, ping-pong)
    - Optimized with monolithic SRAM
    """
    results = []

    print("\n" + "="*80)
    print("  ANALYTICAL MODEL - PAYLOAD SWEEP")
    print("="*80)
    print(f"\nTesting payloads: {payloads}")
    print(f"Channels: {num_channels}")
    print("\n" + "="*80 + "\n")

    for payload in payloads:
        print(f"\nPayload: {payload} bytes ({payload // 64} beats)")
        print("-" * 80)

        # Baseline
        config_base = AXIConfig(
            payload=payload,
            pipeline_depth=1,
            pipelining_enabled=False,
            streaming_drain=False,
            sram_mode="pingpong"
        )
        perf_base = AXI4Performance(config_base)
        result_base = perf_base.calculate_channel_bandwidth(num_channels)

        # Optimized (ping-pong SRAM, limited to depth=2)
        config_opt_pp = AXIConfig(
            payload=payload,
            pipeline_depth=4,  # Will be limited by SRAM
            pipelining_enabled=True,
            streaming_drain=True,
            sram_mode="pingpong"
        )
        perf_opt_pp = AXI4Performance(config_opt_pp)
        result_opt_pp = perf_opt_pp.calculate_channel_bandwidth(num_channels)

        # Optimized (monolithic SRAM, full depth=4 possible)
        config_opt_mono = AXIConfig(
            payload=payload,
            pipeline_depth=4,
            pipelining_enabled=True,
            streaming_drain=True,
            sram_mode="monolithic"
        )
        perf_opt_mono = AXI4Performance(config_opt_mono)
        result_opt_mono = perf_opt_mono.calculate_channel_bandwidth(num_channels)

        # Calculate SRAM requirements
        sram_pp = config_opt_pp.max_sram_pipeline_depth * payload / 1024  # KB
        sram_mono = config_opt_mono.max_sram_pipeline_depth * payload / 1024  # KB

        print(f"  Baseline:          {result_base['total_bw']:>7.2f} GB/s  "
              f"(cycles/burst: {result_base['cycles_per_burst']:.0f})")
        print(f"  Optimized PP:      {result_opt_pp['total_bw']:>7.2f} GB/s  "
              f"(depth: {result_opt_pp['effective_pipeline_depth']}, "
              f"SRAM: {sram_pp:.1f} KB/ch)")
        print(f"  Optimized Mono:    {result_opt_mono['total_bw']:>7.2f} GB/s  "
              f"(depth: {result_opt_mono['effective_pipeline_depth']}, "
              f"SRAM: {sram_mono:.1f} KB/ch)")

        improvement_pp = ((result_opt_pp['total_bw'] / result_base['total_bw']) - 1) * 100
        improvement_mono = ((result_opt_mono['total_bw'] / result_base['total_bw']) - 1) * 100
        mono_vs_pp = ((result_opt_mono['total_bw'] / result_opt_pp['total_bw']) - 1) * 100

        print(f"\n  Improvement (PP):  +{improvement_pp:.1f}%")
        print(f"  Improvement (Mono): +{improvement_mono:.1f}%")
        print(f"  Mono vs PP:        +{mono_vs_pp:.1f}%")

        # Store results
        for config_name, result, sram_kb in [
            ("baseline_pp", result_base, 2 * payload / 1024),
            ("optimized_pp", result_opt_pp, sram_pp),
            ("optimized_mono", result_opt_mono, sram_mono)
        ]:
            results.append({
                'payload_bytes': payload,
                'configuration': config_name,
                'bandwidth_gbps': result['total_bw'],
                'per_channel_gbps': result['B_channel'],
                'effective_pipeline_depth': result['effective_pipeline_depth'],
                'sram_limited': result['sram_limited'],
                'sram_per_channel_kb': sram_kb,
                'total_sram_kb': sram_kb * num_channels,
                'cycles_per_burst': result['cycles_per_burst'],
                'limited_by': result['limited_by']
            })

    print("\n" + "="*80 + "\n")

    df = pd.DataFrame(results)
    return df


def run_simpy_payload_sweep(payloads: List[int] = [256, 512, 1024, 2048],
                            num_channels: int = 16,
                            simulation_time: int = 50000) -> pd.DataFrame:
    """
    Run SimPy simulation across different payload sizes.

    Note: Shorter simulation time for speed (50k instead of 100k cycles)
    """
    results = []

    print("\n" + "="*80)
    print("  SIMPY SIMULATION - PAYLOAD SWEEP")
    print("="*80)
    print(f"\nTesting payloads: {payloads}")
    print(f"Channels: {num_channels}")
    print(f"Simulation time: {simulation_time:,} cycles")
    print("\n" + "="*80 + "\n")

    for payload in payloads:
        print(f"\nPayload: {payload} bytes - Running 3 configurations...")

        # Baseline
        result_base = run_baseline_simulation(
            num_channels=num_channels,
            simulation_time=simulation_time,
            payload=payload,
            verbose=False
        )

        # Optimized with ping-pong
        result_opt_pp = run_optimized_simulation(
            num_channels=num_channels,
            simulation_time=simulation_time,
            payload=payload,
            pipeline_depth=4,
            streaming=True,
            monolithic=False,
            verbose=False
        )

        # Optimized with monolithic
        result_opt_mono = run_optimized_simulation(
            num_channels=num_channels,
            simulation_time=simulation_time,
            payload=payload,
            pipeline_depth=4,
            streaming=True,
            monolithic=True,
            verbose=False
        )

        print(f"  Baseline:       {result_base['aggregate_bandwidth']:>7.2f} GB/s")
        print(f"  Optimized PP:   {result_opt_pp['aggregate_bandwidth']:>7.2f} GB/s")
        print(f"  Optimized Mono: {result_opt_mono['aggregate_bandwidth']:>7.2f} GB/s")

        # Store results
        for config_name, result in [
            ("baseline_pp", result_base),
            ("optimized_pp", result_opt_pp),
            ("optimized_mono", result_opt_mono)
        ]:
            results.append({
                'payload_bytes': payload,
                'configuration': config_name,
                'bandwidth_gbps': result['aggregate_bandwidth'],
                'per_channel_gbps': result['avg_channel_bandwidth'],
                'total_bursts': result['total_bursts'],
                'pipeline_depth': result['config']['pipeline_depth'],
                'streaming': result['config']['streaming_drain'],
                'sram_mode': result['config']['sram_mode']
            })

    print("\n" + "="*80 + "\n")

    df = pd.DataFrame(results)
    return df


def print_summary_table(df: pd.DataFrame):
    """Print formatted summary table."""
    print("\n" + "="*80)
    print("  PAYLOAD SWEEP - SUMMARY TABLE")
    print("="*80 + "\n")

    # Pivot table for easier reading
    pivot = df.pivot(index='payload_bytes', columns='configuration', values='bandwidth_gbps')

    # Reorder columns
    col_order = ['baseline_pp', 'optimized_pp', 'optimized_mono']
    pivot = pivot[col_order]

    # Calculate improvements
    pivot['PP_improvement_%'] = ((pivot['optimized_pp'] / pivot['baseline_pp']) - 1) * 100
    pivot['Mono_improvement_%'] = ((pivot['optimized_mono'] / pivot['baseline_pp']) - 1) * 100
    pivot['Mono_vs_PP_%'] = ((pivot['optimized_mono'] / pivot['optimized_pp']) - 1) * 100

    print(pivot.to_string(float_format=lambda x: f"{x:.2f}"))
    print("\n" + "="*80 + "\n")

    # Key findings
    print("KEY FINDINGS:")
    print("-" * 80)

    # Find payload with biggest monolithic advantage
    max_mono_gain_idx = pivot['Mono_vs_PP_%'].idxmax()
    max_mono_gain = pivot.loc[max_mono_gain_idx, 'Mono_vs_PP_%']

    print(f"\n1. Monolithic SRAM Advantage:")
    print(f"   Biggest gain at {max_mono_gain_idx}B payload: +{max_mono_gain:.1f}% vs ping-pong")
    print(f"   Reason: Smaller payloads allow higher pipeline depth with monolithic SRAM")

    # Check which configs meet 50 GB/s target
    print(f"\n2. Meeting 50 GB/s Target:")
    for payload in pivot.index:
        base_bw = pivot.loc[payload, 'baseline_pp']
        pp_bw = pivot.loc[payload, 'optimized_pp']
        mono_bw = pivot.loc[payload, 'optimized_mono']

        status_base = "✓" if base_bw >= 50 else "✗"
        status_pp = "✓" if pp_bw >= 50 else "✗"
        status_mono = "✓" if mono_bw >= 50 else "✗"

        print(f"   {payload:>4}B: Baseline {status_base}  |  PP {status_pp}  |  Mono {status_mono}")

    print("\n" + "="*80 + "\n")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Run payload size sweep analysis")
    parser.add_argument('--analytical-only', action='store_true',
                       help='Only run analytical model (faster)')
    parser.add_argument('--simpy-only', action='store_true',
                       help='Only run SimPy simulation')
    parser.add_argument('--payloads', type=int, nargs='+',
                       default=[256, 512, 1024, 2048],
                       help='Payload sizes to test (default: 256 512 1024 2048)')
    parser.add_argument('--channels', type=int, default=16,
                       help='Number of channels (default: 16)')
    parser.add_argument('--save-csv', action='store_true',
                       help='Save results to CSV files')

    args = parser.parse_args()

    # Run analyses
    if not args.simpy_only:
        df_analytical = run_analytical_payload_sweep(
            payloads=args.payloads,
            num_channels=args.channels
        )
        print_summary_table(df_analytical)

        if args.save_csv:
            # Ensure csv directory exists
            os.makedirs('csv', exist_ok=True)
            filename = 'csv/payload_sweep_analytical.csv'
            df_analytical.to_csv(filename, index=False)
            print(f"Analytical results saved to: {filename}\n")

    if not args.analytical_only:
        df_simpy = run_simpy_payload_sweep(
            payloads=args.payloads,
            num_channels=args.channels
        )
        print_summary_table(df_simpy)

        if args.save_csv:
            # Ensure csv directory exists
            os.makedirs('csv', exist_ok=True)
            filename = 'csv/payload_sweep_simpy.csv'
            df_simpy.to_csv(filename, index=False)
            print(f"SimPy results saved to: {filename}\n")
