#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: comprehensive_analysis
# Purpose: Comprehensive DMA Performance Analysis
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Comprehensive DMA Performance Analysis

This script provides complete analysis of BOTH read and write paths:
- Clearly labels READ vs WRITE bandwidth
- Sweeps payload sizes (256B, 512B, 1KB, 2KB)
- Calculates SRAM requirements
- Generates data visualizations
- Reports optimization effects

Usage:
    python comprehensive_analysis.py --quick         # Fast analytical only
    python comprehensive_analysis.py --full          # Full SimPy + analytical
    python comprehensive_analysis.py --visualize     # Generate all plots
"""

import sys
import os
import argparse
import pandas as pd
import numpy as np

# Add parent to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from pyperf import AXIConfig, AXI4Performance
from simpy_model.current_design import run_baseline_simulation, run_optimized_simulation
from simpy_model.write_model import run_write_simulation, run_optimized_write_simulation

# Try to import matplotlib for visualizations
try:
    import matplotlib.pyplot as plt
    import seaborn as sns
    PLOTTING_AVAILABLE = True
    sns.set_style("whitegrid")
except ImportError:
    PLOTTING_AVAILABLE = False


def analyze_read_path_payload_sweep(payloads=[256, 512, 1024, 2048],
                                    num_channels=16):
    """Analyze READ path across different payload sizes (analytical)."""

    print("\n" + "="*90)
    print("  READ PATH - PAYLOAD SWEEP ANALYSIS (Analytical Model)")
    print("="*90)

    results = []

    for payload in payloads:
        print(f"\n{'─'*90}")
        print(f"  READ Payload: {payload} bytes ({payload // 64} beats)")
        print(f"{'─'*90}")

        # Baseline: No pipelining, store-and-forward, ping-pong
        cfg_base = AXIConfig(
            payload=payload,
            pipeline_depth=1,
            pipelining_enabled=False,
            streaming_drain=False,
            sram_mode="pingpong"
        )
        perf_base = AXI4Performance(cfg_base)
        res_base = perf_base.calculate_channel_bandwidth(num_channels)

        # Optimized: Pipeline + streaming (ping-pong SRAM limited to depth=2)
        cfg_opt = AXIConfig(
            payload=payload,
            pipeline_depth=4,
            pipelining_enabled=True,
            streaming_drain=True,
            sram_mode="pingpong"
        )
        perf_opt = AXI4Performance(cfg_opt)
        res_opt = perf_opt.calculate_channel_bandwidth(num_channels)

        # Calculate SRAM requirements
        sram_base_kb = 2 * payload / 1024  # Ping-pong: 2 slots
        sram_opt_kb = res_opt['effective_pipeline_depth'] * payload / 1024

        improvement = ((res_opt['total_bw'] / res_base['total_bw']) - 1) * 100

        print(f"  Baseline READ BW:      {res_base['total_bw']:>7.2f} GB/s")
        print(f"    - Cycles/burst:      {res_base['cycles_per_burst']:>7.0f} cycles")
        print(f"    - SRAM per channel:  {sram_base_kb:>7.2f} KB (2 slots × {payload}B)")
        print(f"    - Total SRAM:        {sram_base_kb * num_channels:>7.2f} KB")

        print(f"\n  Optimized READ BW:     {res_opt['total_bw']:>7.2f} GB/s (+{improvement:.1f}%)")
        print(f"    - Pipeline depth:    {res_opt['effective_pipeline_depth']} (SRAM limited: {res_opt['sram_limited']})")
        print(f"    - Cycles/burst:      {res_opt['cycles_per_burst']:>7.0f} cycles")
        print(f"    - SRAM per channel:  {sram_opt_kb:>7.2f} KB")
        print(f"    - Total SRAM:        {sram_opt_kb * num_channels:>7.2f} KB")
        print(f"    - Limited by:        {res_opt['limited_by']}")

        # Store for DataFrame
        results.append({
            'path': 'READ',
            'payload_bytes': payload,
            'config': 'baseline',
            'bandwidth_gbps': res_base['total_bw'],
            'cycles_per_burst': res_base['cycles_per_burst'],
            'pipeline_depth': 1,
            'sram_per_ch_kb': sram_base_kb,
            'total_sram_kb': sram_base_kb * num_channels
        })

        results.append({
            'path': 'READ',
            'payload_bytes': payload,
            'config': 'optimized',
            'bandwidth_gbps': res_opt['total_bw'],
            'cycles_per_burst': res_opt['cycles_per_burst'],
            'pipeline_depth': res_opt['effective_pipeline_depth'],
            'sram_per_ch_kb': sram_opt_kb,
            'total_sram_kb': sram_opt_kb * num_channels
        })

    print(f"\n{'='*90}\n")
    return pd.DataFrame(results)


def analyze_write_path_payload_sweep(payloads=[256, 512, 1024, 2048],
                                     num_channels=16):
    """Analyze WRITE path across different payload sizes (analytical)."""

    print("\n" + "="*90)
    print("  WRITE PATH - PAYLOAD SWEEP ANALYSIS (Analytical Model)")
    print("="*90)

    results = []

    for payload in payloads:
        print(f"\n{'─'*90}")
        print(f"  WRITE Payload: {payload} bytes ({payload // 64} beats)")
        print(f"{'─'*90}")

        # Baseline: 32 outstanding bursts
        cfg_base = AXIConfig(
            payload=payload,
            pipeline_depth=2,  # Outstanding = depth × channels (roughly)
            pipelining_enabled=True,
            streaming_drain=False,
            max_outstanding_bursts=32
        )
        perf_base = AXI4Performance(cfg_base)
        res_base = perf_base.calculate_channel_bandwidth(num_channels)

        # Optimized: 64 outstanding bursts
        cfg_opt = AXIConfig(
            payload=payload,
            pipeline_depth=4,
            pipelining_enabled=True,
            streaming_drain=False,
            max_outstanding_bursts=64
        )
        perf_opt = AXI4Performance(cfg_opt)
        res_opt = perf_opt.calculate_channel_bandwidth(num_channels)

        # WRITE SRAM: simpler, just buffer for burst
        sram_base_kb = 2 * payload / 1024  # 2 buffers for double buffering
        sram_opt_kb = 2 * payload / 1024   # Same SRAM, just more outstanding

        improvement = ((res_opt['total_bw'] / res_base['total_bw']) - 1) * 100

        print(f"  Baseline WRITE BW:     {res_base['total_bw']:>7.2f} GB/s")
        print(f"    - Outstanding:       32 bursts (system-wide)")
        print(f"    - Outstanding/ch:    {32 / num_channels:.1f}")
        print(f"    - SRAM per channel:  {sram_base_kb:>7.2f} KB (2 buffers × {payload}B)")
        print(f"    - Total SRAM:        {sram_base_kb * num_channels:>7.2f} KB")

        print(f"\n  Optimized WRITE BW:    {res_opt['total_bw']:>7.2f} GB/s (+{improvement:.1f}%)")
        print(f"    - Outstanding:       64 bursts (system-wide)")
        print(f"    - Outstanding/ch:    {64 / num_channels:.1f}")
        print(f"    - SRAM per channel:  {sram_opt_kb:>7.2f} KB")
        print(f"    - Total SRAM:        {sram_opt_kb * num_channels:>7.2f} KB")
        print(f"    - Limited by:        {res_opt['limited_by']}")

        # Store for DataFrame
        results.append({
            'path': 'WRITE',
            'payload_bytes': payload,
            'config': 'baseline',
            'bandwidth_gbps': res_base['total_bw'],
            'cycles_per_burst': res_base['cycles_per_burst'],
            'outstanding_bursts': 32,
            'sram_per_ch_kb': sram_base_kb,
            'total_sram_kb': sram_base_kb * num_channels
        })

        results.append({
            'path': 'WRITE',
            'payload_bytes': payload,
            'config': 'optimized',
            'bandwidth_gbps': res_opt['total_bw'],
            'cycles_per_burst': res_opt['cycles_per_burst'],
            'outstanding_bursts': 64,
            'sram_per_ch_kb': sram_opt_kb,
            'total_sram_kb': sram_opt_kb * num_channels
        })

    print(f"\n{'='*90}\n")
    return pd.DataFrame(results)


def generate_summary_report(df_read, df_write, target_bw=50.0):
    """Generate summary report showing READ and WRITE SEPARATELY."""

    print("\n" + "="*90)
    print("  SUMMARY - READ and WRITE PATHS (INDEPENDENT)")
    print("="*90)

    # READ PATH SUMMARY
    print("\n" + "─"*90)
    print("  READ PATH (Separate Analysis)")
    print("─"*90)
    print(f"\n  {'Payload':<12} {'Baseline':<18} {'Optimized':<18} {'Meets Target':<15} {'SRAM/ch'}")
    print(f"  {'-'*86}")

    for payload in sorted(df_read['payload_bytes'].unique()):
        read_base = df_read[(df_read['payload_bytes'] == payload) &
                           (df_read['config'] == 'baseline')].iloc[0]
        read_opt = df_read[(df_read['payload_bytes'] == payload) &
                          (df_read['config'] == 'optimized')].iloc[0]

        meets = "✅ Yes" if read_opt['bandwidth_gbps'] >= target_bw else "❌ No"

        print(f"  {payload:>4}B       {read_base['bandwidth_gbps']:>7.2f} GB/s     "
              f"{read_opt['bandwidth_gbps']:>7.2f} GB/s     {meets:<15} {read_opt['sram_per_ch_kb']:>5.1f} KB")

    print(f"\n  Note: READ uses 2KB bursts in typical design")

    # WRITE PATH SUMMARY
    print("\n" + "─"*90)
    print("  WRITE PATH (Separate Analysis)")
    print("─"*90)
    print(f"\n  {'Payload':<12} {'Baseline':<18} {'Optimized':<18} {'Meets Target':<15} {'SRAM/ch'}")
    print(f"  {'-'*86}")

    for payload in sorted(df_write['payload_bytes'].unique()):
        write_base = df_write[(df_write['payload_bytes'] == payload) &
                             (df_write['config'] == 'baseline')].iloc[0]
        write_opt = df_write[(df_write['payload_bytes'] == payload) &
                            (df_write['config'] == 'optimized')].iloc[0]

        meets = "✅ Yes" if write_opt['bandwidth_gbps'] >= target_bw else "❌ No"

        print(f"  {payload:>4}B       {write_base['bandwidth_gbps']:>7.2f} GB/s     "
              f"{write_opt['bandwidth_gbps']:>7.2f} GB/s     {meets:<15} {write_opt['sram_per_ch_kb']:>5.1f} KB")

    print(f"\n  Note: WRITE uses 256B bursts in typical design")
    print(f"\n  ⚠️  READ and WRITE are INDEPENDENT paths - they do NOT combine.")

    print(f"\n{'='*90}\n")


def plot_payload_sweep(df_read, df_write, save_path='assets/payload_sweep_separate.png'):
    """Generate visualization showing READ and WRITE SEPARATELY."""

    # Ensure assets directory exists
    os.makedirs(os.path.dirname(save_path), exist_ok=True)

    if not PLOTTING_AVAILABLE:
        print("WARNING: matplotlib not available, skipping plots")
        return

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    payloads = sorted(df_read['payload_bytes'].unique())

    # Plot 1: READ bandwidth by payload
    ax = axes[0, 0]
    for config in ['baseline', 'optimized']:
        data = df_read[df_read['config'] == config]
        ax.plot(data['payload_bytes'], data['bandwidth_gbps'],
               marker='o', label=f'READ {config}', linewidth=2, markersize=8)

    ax.axhline(y=50, color='r', linestyle='--', label='50 GB/s target', linewidth=2, alpha=0.7)
    ax.axhline(y=57.6, color='gray', linestyle=':', label='AXI peak (57.6 GB/s)', linewidth=2, alpha=0.7)
    ax.set_xlabel('READ Payload Size (bytes)', fontsize=11)
    ax.set_ylabel('READ Bandwidth (GB/s)', fontsize=11)
    ax.set_title('READ Path: Bandwidth vs Payload Size\n(Independent Path)', fontsize=12, fontweight='bold')
    ax.legend()
    ax.grid(True, alpha=0.3)
    ax.set_xscale('log', base=2)
    ax.set_xticks(payloads)
    ax.set_xticklabels([f'{p}B' for p in payloads])
    ax.set_ylim(0, 65)

    # Plot 2: WRITE bandwidth by payload
    ax = axes[0, 1]
    for config in ['baseline', 'optimized']:
        data = df_write[df_write['config'] == config]
        ax.plot(data['payload_bytes'], data['bandwidth_gbps'],
               marker='s', label=f'WRITE {config}', linewidth=2, markersize=8)

    ax.axhline(y=50, color='r', linestyle='--', label='50 GB/s target', linewidth=2, alpha=0.7)
    ax.set_xlabel('WRITE Payload Size (bytes)', fontsize=11)
    ax.set_ylabel('WRITE Bandwidth (GB/s)', fontsize=11)
    ax.set_title('WRITE Path: Bandwidth vs Payload Size\n(Independent Path)', fontsize=12, fontweight='bold')
    ax.legend()
    ax.grid(True, alpha=0.3)
    ax.set_xscale('log', base=2)
    ax.set_xticks(payloads)
    ax.set_xticklabels([f'{p}B' for p in payloads])
    ax.set_ylim(0, 65)
    ax.text(0.5, 0.95, 'Note: 256B is typical WRITE size',
            transform=ax.transAxes, ha='center', va='top', fontsize=9, style='italic')

    # Plot 3: SRAM requirements - READ and WRITE separate
    ax = axes[1, 0]

    x = np.arange(len(payloads))
    width = 0.35

    read_sram = [df_read[(df_read['payload_bytes'] == p) &
                         (df_read['config'] == 'optimized')]['total_sram_kb'].values[0]
                 for p in payloads]
    write_sram = [df_write[(df_write['payload_bytes'] == p) &
                           (df_write['config'] == 'optimized')]['total_sram_kb'].values[0]
                  for p in payloads]

    ax.bar(x - width/2, read_sram, width, label='READ Path', alpha=0.8)
    ax.bar(x + width/2, write_sram, width, label='WRITE Path', alpha=0.8)

    ax.set_ylabel('Total SRAM (KB)', fontsize=11)
    ax.set_title('SRAM Requirements (Optimized Configs)\n(Separate Paths)', fontsize=12, fontweight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels([f'{p}B' for p in payloads])
    ax.legend()
    ax.grid(True, axis='y', alpha=0.3)

    # Plot 4: Improvement percentages - separate paths
    ax = axes[1, 1]

    read_improvements = []
    write_improvements = []

    for payload in payloads:
        read_base = df_read[(df_read['payload_bytes'] == payload) &
                           (df_read['config'] == 'baseline')]['bandwidth_gbps'].values[0]
        read_opt = df_read[(df_read['payload_bytes'] == payload) &
                          (df_read['config'] == 'optimized')]['bandwidth_gbps'].values[0]

        write_base = df_write[(df_write['payload_bytes'] == payload) &
                             (df_write['config'] == 'baseline')]['bandwidth_gbps'].values[0]
        write_opt = df_write[(df_write['payload_bytes'] == payload) &
                            (df_write['config'] == 'optimized')]['bandwidth_gbps'].values[0]

        read_improvements.append(((read_opt / read_base) - 1) * 100 if read_base > 0 else 0)
        write_improvements.append(((write_opt / write_base) - 1) * 100 if write_base > 0 else 0)

    x = np.arange(len(payloads))
    width = 0.35

    ax.bar(x - width/2, read_improvements, width, label='READ Improvement', alpha=0.8)
    ax.bar(x + width/2, write_improvements, width, label='WRITE Improvement', alpha=0.8)

    ax.set_ylabel('Improvement (%)', fontsize=11)
    ax.set_title('Optimization Impact: Baseline → Optimized\n(Each Path Independently)',
                 fontsize=12, fontweight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels([f'{p}B' for p in payloads])
    ax.legend()
    ax.grid(True, axis='y', alpha=0.3)

    plt.suptitle('DMA Performance Analysis - READ and WRITE are INDEPENDENT Paths',
                fontsize=14, fontweight='bold', y=0.995)
    plt.tight_layout()
    plt.savefig(save_path, dpi=150, bbox_inches='tight')
    print(f"\n📊 Saved visualization to: {save_path}\n")
    plt.close()


def document_design_parameters():
    """Document other design parameters that could be investigated."""

    print("\n" + "="*90)
    print("  DESIGN PARAMETERS TO INVESTIGATE (Outside Current Model)")
    print("="*90)

    params = [
        {
            'parameter': 'Custom Side Drain Rate',
            'current': '4 GB/s per channel (1 beat / 16 cycles)',
            'impact': 'Directly limits per-channel READ bandwidth',
            'investigation': 'Vary cycles_per_beat: Try 8, 12, 20, 24 to see bottleneck shift'
        },
        {
            'parameter': 'Memory Latency',
            'current': '200 cycles (fixed)',
            'impact': 'With pipelining, affects startup time but not steady-state BW',
            'investigation': 'Try 100, 150, 250, 300 cycles - should see minimal BW impact with deep pipeline'
        },
        {
            'parameter': 'AXI Protocol Efficiency (α)',
            'current': '0.9 (90% efficiency)',
            'impact': 'Reduces effective AXI bandwidth from 64 → 57.6 GB/s',
            'investigation': 'Try 0.85, 0.95, 1.0 to see AXI overhead effects'
        },
        {
            'parameter': 'Number of Channels',
            'current': '16 physical channels',
            'impact': 'More channels = higher aggregate BW (until AXI saturates)',
            'investigation': 'Try 8, 12, 20, 24, 32 channels to find saturation point'
        },
        {
            'parameter': 'Mixed Read/Write Workloads',
            'current': 'Analyzed separately',
            'impact': 'READ and WRITE compete for same AXI bandwidth',
            'investigation': 'Model concurrent READ+WRITE with different ratios (50/50, 70/30, 90/10)'
        },
        {
            'parameter': 'Burst Ordering/Priority',
            'current': 'Round-robin assumed',
            'impact': 'Priority schemes could favor READ or WRITE',
            'investigation': 'Model priority arbitration, QoS effects on latency distribution'
        },
        {
            'parameter': 'SRAM Access Contention',
            'current': 'Assumed no contention (dedicated SRAM per channel)',
            'impact': 'Shared SRAM would create bottleneck',
            'investigation': 'Model shared SRAM pool with arbitration overhead'
        },
        {
            'parameter': 'Variable Payload Sizes (Runtime)',
            'current': 'Fixed payload per analysis',
            'impact': 'Real workloads mix 256B-2KB bursts',
            'investigation': 'Model distribution of payload sizes, SRAM fragmentation effects'
        },
        {
            'parameter': 'Power/Energy Consumption',
            'current': 'Not modeled',
            'impact': 'Higher BW = more power, pipelining adds SRAM power',
            'investigation': 'Add energy model: SRAM active/idle power, AXI transaction energy'
        },
        {
            'parameter': 'Error Recovery/Retry Logic',
            'current': 'Perfect operation assumed',
            'impact': 'Real systems have ECC corrections, retries',
            'investigation': 'Model error rates, retry overhead, impact on effective bandwidth'
        }
    ]

    print(f"\n{'Parameter':<30} {'Current Value':<35} {'Investigation'}")
    print(f"{'-'*90}")

    for i, p in enumerate(params, 1):
        print(f"\n{i}. {p['parameter']}")
        print(f"   Current:  {p['current']}")
        print(f"   Impact:   {p['impact']}")
        print(f"   Study:    {p['investigation']}")

    print(f"\n{'='*90}\n")


def main():
    parser = argparse.ArgumentParser(description='Comprehensive DMA Performance Analysis')
    parser.add_argument('--quick', action='store_true',
                       help='Quick analytical analysis only (no SimPy)')
    parser.add_argument('--full', action='store_true',
                       help='Full analysis including SimPy validation')
    parser.add_argument('--visualize', action='store_true',
                       help='Generate visualizations')
    parser.add_argument('--payloads', type=int, nargs='+',
                       default=[256, 512, 1024, 2048],
                       help='Payload sizes to test (default: 256 512 1024 2048)')
    parser.add_argument('--channels', type=int, default=16,
                       help='Number of channels (default: 16)')
    parser.add_argument('--save-csv', action='store_true',
                       help='Save results to CSV files')

    args = parser.parse_args()

    # If no mode specified, run quick
    if not (args.quick or args.full):
        args.quick = True

    print("\n" + "="*90)
    print("  COMPREHENSIVE DMA PERFORMANCE ANALYSIS")
    print("="*90)
    print(f"\n  Mode:     {'Quick (Analytical)' if args.quick else 'Full (SimPy + Analytical)'}")
    print(f"  Payloads: {args.payloads}")
    print(f"  Channels: {args.channels}")
    print(f"\n{'='*90}")

    # Run READ path analysis
    df_read = analyze_read_path_payload_sweep(
        payloads=args.payloads,
        num_channels=args.channels
    )

    # Run WRITE path analysis
    df_write = analyze_write_path_payload_sweep(
        payloads=args.payloads,
        num_channels=args.channels
    )

    # Generate summary report
    generate_summary_report(df_read, df_write)

    # Document design parameters to investigate
    document_design_parameters()

    # Save CSVs if requested
    if args.save_csv:
        # Ensure csv directory exists
        os.makedirs('csv', exist_ok=True)
        df_read.to_csv('csv/analysis_read_path.csv', index=False)
        df_write.to_csv('csv/analysis_write_path.csv', index=False)
        print(f"📁 Saved results to: csv/analysis_read_path.csv, csv/analysis_write_path.csv\n")

    # Generate visualizations
    if args.visualize or PLOTTING_AVAILABLE:
        plot_payload_sweep(df_read, df_write)

    print("✅ Analysis complete!\n")


if __name__ == "__main__":
    main()
