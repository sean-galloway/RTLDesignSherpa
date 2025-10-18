#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: generate_optimization_plots
# Purpose: Generate Optimization Effect Visualizations
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Generate Optimization Effect Visualizations

This script creates detailed visualizations showing the effect of each optimization:
- Baseline vs each individual optimization
- Combined optimization effects
- Bottleneck analysis
- SRAM vs performance tradeoffs
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
from pyperf import AXIConfig, AXI4Performance

sns.set_style("whitegrid")
sns.set_palette("husl")


def analyze_read_optimizations(payload=2048, num_channels=16):
    """Analyze each READ optimization independently."""

    configs = {
        '1. Baseline\n(No Pipeline,\nStore-and-Forward)': AXIConfig(
            payload=payload,
            pipeline_depth=1,
            pipelining_enabled=False,
            streaming_drain=False,
            sram_mode="pingpong"
        ),
        '2. Streaming\nDrain Only': AXIConfig(
            payload=payload,
            pipeline_depth=1,
            pipelining_enabled=False,
            streaming_drain=True,
            sram_mode="pingpong"
        ),
        '3. Pipeline\nDepth=2': AXIConfig(
            payload=payload,
            pipeline_depth=2,
            pipelining_enabled=True,
            streaming_drain=False,
            sram_mode="pingpong"
        ),
        '4. Pipeline\nDepth=4\n(SRAM limited)': AXIConfig(
            payload=payload,
            pipeline_depth=4,
            pipelining_enabled=True,
            streaming_drain=False,
            sram_mode="pingpong"
        ),
        '5. Pipeline +\nStreaming': AXIConfig(
            payload=payload,
            pipeline_depth=4,
            pipelining_enabled=True,
            streaming_drain=True,
            sram_mode="pingpong"
        ),
    }

    results = {}
    for name, config in configs.items():
        perf = AXI4Performance(config)
        res = perf.calculate_channel_bandwidth(num_channels)
        results[name] = {
            'bandwidth': res['total_bw'],
            'cycles_per_burst': res['cycles_per_burst'],
            'pipeline_depth': res['effective_pipeline_depth'],
            'limited_by': res['limited_by'],
            'sram_kb': res['effective_pipeline_depth'] * payload / 1024
        }

    return results


def plot_optimization_waterfall(results, save_path='assets/optimization_waterfall.png'):
    """Create waterfall chart showing incremental optimization effects."""

    # Ensure assets directory exists
    os.makedirs(os.path.dirname(save_path), exist_ok=True)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 6))

    # Extract data
    names = list(results.keys())
    bandwidths = [results[name]['bandwidth'] for name in names]
    cycles = [results[name]['cycles_per_burst'] for name in names]

    baseline_bw = bandwidths[0]
    improvements = [((bw / baseline_bw) - 1) * 100 for bw in bandwidths]

    # Plot 1: Bandwidth progression
    colors = ['red' if i == 0 else 'green' if i == len(names)-1 else 'steelblue'
              for i in range(len(names))]

    bars1 = ax1.bar(range(len(names)), bandwidths, color=colors, alpha=0.7, edgecolor='black')

    # Add target line
    ax1.axhline(y=50, color='orange', linestyle='--', linewidth=2,
                label='50 GB/s Target', alpha=0.8)
    ax1.axhline(y=57.6, color='gray', linestyle=':', linewidth=2,
                label='AXI Peak (57.6 GB/s)', alpha=0.8)

    # Add value labels on bars
    for i, (bar, bw, improvement) in enumerate(zip(bars1, bandwidths, improvements)):
        height = bar.get_height()
        label = f'{bw:.1f} GB/s'
        if i > 0:
            label += f'\n(+{improvement:.1f}%)'
        ax1.text(bar.get_x() + bar.get_width()/2., height,
                label, ha='center', va='bottom', fontsize=9, fontweight='bold')

    ax1.set_ylabel('READ Bandwidth (GB/s)', fontsize=12, fontweight='bold')
    ax1.set_title(f'READ Path Optimization Progression\n(Payload={results[names[0]]["cycles_per_burst"]} bytes, 16 channels)',
                 fontsize=13, fontweight='bold')
    ax1.set_xticks(range(len(names)))
    ax1.set_xticklabels(names, fontsize=9, ha='center')
    ax1.legend(loc='upper left', fontsize=10)
    ax1.grid(True, alpha=0.3, axis='y')
    ax1.set_ylim(0, 65)

    # Plot 2: Cycles per burst reduction
    bars2 = ax2.bar(range(len(names)), cycles, color=colors, alpha=0.7, edgecolor='black')

    for i, (bar, cyc) in enumerate(zip(bars2, cycles)):
        height = bar.get_height()
        reduction = ((cyc / cycles[0]) - 1) * 100 if i > 0 else 0
        label = f'{cyc:.0f} cyc'
        if i > 0:
            label += f'\n({reduction:.0f}%)'
        ax2.text(bar.get_x() + bar.get_width()/2., height,
                label, ha='center', va='bottom', fontsize=9, fontweight='bold')

    ax2.set_ylabel('Cycles per Burst', fontsize=12, fontweight='bold')
    ax2.set_title('Timing Improvement\n(Lower is Better)', fontsize=13, fontweight='bold')
    ax2.set_xticks(range(len(names)))
    ax2.set_xticklabels(names, fontsize=9, ha='center')
    ax2.grid(True, alpha=0.3, axis='y')
    ax2.invert_yaxis()  # Invert so lower cycles is visually "better"

    plt.tight_layout()
    plt.savefig(save_path, dpi=150, bbox_inches='tight')
    print(f"📊 Saved optimization waterfall to: {save_path}")
    plt.close()


def plot_bottleneck_analysis(save_path='assets/bottleneck_analysis.png'):
    """Show where each configuration is bottlenecked."""

    # Ensure assets directory exists
    os.makedirs(os.path.dirname(save_path), exist_ok=True)

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    payloads = [256, 512, 1024, 2048]

    for idx, payload in enumerate(payloads):
        ax = axes[idx // 2, idx % 2]

        # Test different pipeline depths
        depths = [1, 2, 4, 8, 16]
        bw_no_stream = []
        bw_stream = []
        limiting_factors = []

        for depth in depths:
            # Without streaming
            cfg_no = AXIConfig(payload=payload, pipeline_depth=depth,
                              pipelining_enabled=(depth > 1), streaming_drain=False,
                              sram_mode="monolithic")  # Use monolithic to allow higher depths
            perf_no = AXI4Performance(cfg_no)
            res_no = perf_no.calculate_channel_bandwidth(16)
            bw_no_stream.append(res_no['total_bw'])

            # With streaming
            cfg_yes = AXIConfig(payload=payload, pipeline_depth=depth,
                               pipelining_enabled=(depth > 1), streaming_drain=True,
                               sram_mode="monolithic")
            perf_yes = AXI4Performance(cfg_yes)
            res_yes = perf_yes.calculate_channel_bandwidth(16)
            bw_stream.append(res_yes['total_bw'])
            limiting_factors.append(res_yes['limited_by'])

        ax.plot(depths, bw_no_stream, 'o-', label='Store-and-Forward', linewidth=2, markersize=8)
        ax.plot(depths, bw_stream, 's-', label='Streaming', linewidth=2, markersize=8)

        # Add horizontal lines for limits
        ax.axhline(y=50, color='orange', linestyle='--', label='50 GB/s Target', alpha=0.6)
        ax.axhline(y=57.6, color='gray', linestyle=':', label='AXI Peak', alpha=0.6)

        # Add limiting factor annotations
        for i, (depth, limit) in enumerate(zip(depths, limiting_factors)):
            if 'AXI' in limit and i > 0:
                ax.annotate('AXI Limited', xy=(depth, 57.6), xytext=(depth, 60),
                           ha='center', fontsize=7, alpha=0.7)
                break

        ax.set_xlabel('Pipeline Depth', fontsize=10)
        ax.set_ylabel('READ Bandwidth (GB/s)', fontsize=10)
        ax.set_title(f'{payload}B Payload', fontsize=11, fontweight='bold')
        ax.legend(fontsize=8, loc='lower right')
        ax.grid(True, alpha=0.3)
        ax.set_xticks(depths)
        ax.set_ylim(0, 65)

    plt.suptitle('Bottleneck Analysis: Pipeline Depth vs Bandwidth\n(READ Path, 16 channels, Monolithic SRAM)',
                fontsize=13, fontweight='bold')
    plt.tight_layout()
    plt.savefig(save_path, dpi=150, bbox_inches='tight')
    print(f"📊 Saved bottleneck analysis to: {save_path}")
    plt.close()


def plot_sram_vs_performance(save_path='assets/sram_vs_performance.png'):
    """Show SRAM requirements vs performance tradeoff."""

    # Ensure assets directory exists
    os.makedirs(os.path.dirname(save_path), exist_ok=True)

    fig, axes = plt.subplots(1, 2, figsize=(14, 6))

    payloads = [256, 512, 1024, 2048]
    colors = plt.cm.viridis(np.linspace(0, 1, len(payloads)))

    # Plot 1: SRAM vs Bandwidth for different payloads
    ax = axes[0]

    for payload, color in zip(payloads, colors):
        depths = range(1, 9)
        sram_requirements = []
        bandwidths = []

        for depth in depths:
            cfg = AXIConfig(payload=payload, pipeline_depth=depth,
                           pipelining_enabled=(depth > 1), streaming_drain=True,
                           sram_mode="monolithic")
            perf = AXI4Performance(cfg)
            res = perf.calculate_channel_bandwidth(16)

            sram_kb = res['effective_pipeline_depth'] * payload / 1024 * 16  # Total SRAM
            sram_requirements.append(sram_kb)
            bandwidths.append(res['total_bw'])

        ax.plot(sram_requirements, bandwidths, 'o-', label=f'{payload}B payload',
               color=color, linewidth=2, markersize=6)

    ax.axhline(y=50, color='orange', linestyle='--', label='50 GB/s Target', linewidth=2)
    ax.axhline(y=57.6, color='gray', linestyle=':', label='AXI Peak', linewidth=2, alpha=0.7)

    ax.set_xlabel('Total READ SRAM (KB)', fontsize=11, fontweight='bold')
    ax.set_ylabel('READ Bandwidth (GB/s)', fontsize=11, fontweight='bold')
    ax.set_title('SRAM Budget vs Performance\n(READ Path, 16 channels)', fontsize=12, fontweight='bold')
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

    # Plot 2: Cost-benefit analysis (GB/s per KB of SRAM)
    ax = axes[1]

    for payload, color in zip(payloads, colors):
        depths = range(1, 9)
        efficiency = []
        sram_req = []

        for depth in depths:
            cfg = AXIConfig(payload=payload, pipeline_depth=depth,
                           pipelining_enabled=(depth > 1), streaming_drain=True,
                           sram_mode="monolithic")
            perf = AXI4Performance(cfg)
            res = perf.calculate_channel_bandwidth(16)

            sram_kb = res['effective_pipeline_depth'] * payload / 1024 * 16
            if sram_kb > 0:
                eff = res['total_bw'] / sram_kb  # GB/s per KB
                efficiency.append(eff)
                sram_req.append(sram_kb)

        ax.plot(sram_req, efficiency, 'o-', label=f'{payload}B payload',
               color=color, linewidth=2, markersize=6)

    ax.set_xlabel('Total READ SRAM (KB)', fontsize=11, fontweight='bold')
    ax.set_ylabel('Efficiency (GB/s per KB SRAM)', fontsize=11, fontweight='bold')
    ax.set_title('SRAM Efficiency\n(Higher is Better)', fontsize=12, fontweight='bold')
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(save_path, dpi=150, bbox_inches='tight')
    print(f"📊 Saved SRAM vs performance to: {save_path}")
    plt.close()


def plot_write_path_analysis(save_path='assets/write_path_analysis.png'):
    """Analyze WRITE path separately (256B bursts)."""

    # Ensure assets directory exists
    os.makedirs(os.path.dirname(save_path), exist_ok=True)

    fig, axes = plt.subplots(1, 2, figsize=(14, 6))

    # Plot 1: WRITE bandwidth vs outstanding bursts
    ax = axes[0]

    outstanding_vals = [16, 32, 64, 128, 256]
    write_bws = []

    for outstanding in outstanding_vals:
        cfg = AXIConfig(
            payload=256,
            pipeline_depth=outstanding // 16,
            pipelining_enabled=True,
            max_outstanding_bursts=outstanding
        )
        perf = AXI4Performance(cfg)
        result = perf.calculate_channel_bandwidth(16)
        write_bws.append(result['total_bw'])

    ax.plot(outstanding_vals, write_bws, 'o-', linewidth=2, markersize=8, color='orange')
    ax.axhline(y=50, color='r', linestyle='--', label='50 GB/s target', linewidth=2, alpha=0.7)
    ax.axhline(y=20.08, color='gray', linestyle=':', label='Maximum achievable (~20 GB/s)',
              linewidth=2, alpha=0.7)

    ax.set_xlabel('Outstanding Bursts (System-Wide)', fontsize=11, fontweight='bold')
    ax.set_ylabel('WRITE Bandwidth (GB/s)', fontsize=11, fontweight='bold')
    ax.set_title('WRITE Path: Effect of Outstanding Bursts\n(256B bursts, 16 channels)',
                fontsize=12, fontweight='bold')
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)
    ax.set_ylim(0, 65)
    ax.text(0.5, 0.3, 'Limited by small burst size (256B)\nCannot exceed ~20 GB/s',
            transform=ax.transAxes, ha='center', fontsize=10,
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    # Plot 2: WRITE payload size impact
    ax = axes[1]

    write_payloads = [256, 512, 1024, 2048]
    write_bw_by_payload = []

    for payload in write_payloads:
        cfg = AXIConfig(
            payload=payload,
            pipeline_depth=2,
            pipelining_enabled=True,
            max_outstanding_bursts=32
        )
        perf = AXI4Performance(cfg)
        result = perf.calculate_channel_bandwidth(16)
        write_bw_by_payload.append(result['total_bw'])

    ax.plot(write_payloads, write_bw_by_payload, 's-', linewidth=2, markersize=8, color='green')
    ax.axhline(y=50, color='r', linestyle='--', label='50 GB/s target', linewidth=2, alpha=0.7)
    ax.axhline(y=57.6, color='gray', linestyle=':', label='AXI Peak (57.6 GB/s)',
              linewidth=2, alpha=0.7)

    ax.set_xlabel('WRITE Payload Size (bytes)', fontsize=11, fontweight='bold')
    ax.set_ylabel('WRITE Bandwidth (GB/s)', fontsize=11, fontweight='bold')
    ax.set_title('WRITE Path: Effect of Payload Size\n(32 outstanding, 16 channels)',
                fontsize=12, fontweight='bold')
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)
    ax.set_xscale('log', base=2)
    ax.set_xticks(write_payloads)
    ax.set_xticklabels([f'{p}B' for p in write_payloads])
    ax.set_ylim(0, 65)
    ax.text(0.5, 0.3, 'Larger payloads improve WRITE BW\n(typical design uses 256B)',
            transform=ax.transAxes, ha='center', fontsize=10,
            bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.5))

    plt.suptitle('WRITE Path Analysis (Independent from READ)',
                fontsize=14, fontweight='bold', y=0.995)
    plt.tight_layout()
    plt.savefig(save_path, dpi=150, bbox_inches='tight')
    print(f"📊 Saved WRITE path analysis to: {save_path}")
    plt.close()


def main():
    print("\n" + "="*80)
    print("  GENERATING OPTIMIZATION EFFECT VISUALIZATIONS")
    print("="*80 + "\n")

    # Generate all plots
    print("Creating visualizations...\n")

    # 1. Optimization waterfall (2KB payload)
    results_2kb = analyze_read_optimizations(payload=2048, num_channels=16)
    plot_optimization_waterfall(results_2kb)

    # 2. Bottleneck analysis (all payloads)
    plot_bottleneck_analysis()

    # 3. SRAM vs performance tradeoffs
    plot_sram_vs_performance()

    # 4. WRITE path analysis (separate from READ)
    plot_write_path_analysis()

    print("\n" + "="*80)
    print("  ✅ All visualizations generated!")
    print("="*80 + "\n")

    print("Generated files (in assets/ directory):")
    print("  1. assets/optimization_waterfall.png      - Step-by-step READ optimization effects")
    print("  2. assets/bottleneck_analysis.png         - Where READ configs hit limits")
    print("  3. assets/sram_vs_performance.png         - SRAM cost vs READ bandwidth gained")
    print("  4. assets/write_path_analysis.png         - WRITE path independent analysis")
    print("\n  Note: READ and WRITE are INDEPENDENT paths")
    print("\n")


if __name__ == "__main__":
    main()
