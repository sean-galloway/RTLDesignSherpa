# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: comprehensive_analysis
# Purpose: STREAM DMA Comprehensive Performance Analysis
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-18

"""
STREAM DMA Comprehensive Performance Analysis

Analyzes STREAM DMA performance across Low, Medium, and High performance modes
with separate read and write path analysis.

Usage:
    python comprehensive_analysis.py              # Run full analysis
    python comprehensive_analysis.py --mode LOW   # Analyze specific mode
    python comprehensive_analysis.py --plots      # Generate plots
"""

import sys
import os
import argparse
import pandas as pd

# Add pyperf to path
sys.path.insert(0, os.path.dirname(__file__))

from pyperf import (
    AXIConfig, AXI4Performance, StreamDMAConfig, StreamDMAPerformance,
    PerformanceMode, create_mode_configs, LOW_PERF_CONFIG,
    MEDIUM_PERF_CONFIG, HIGH_PERF_CONFIG, DEFAULT_PAYLOAD_OPTIONS,
    show_defaults, PerformanceGraphs
)


def analyze_single_mode(mode: PerformanceMode, payload: int = 1024, verbose: bool = True):
    """
    Analyze performance for a single mode.

    Args:
        mode: PerformanceMode (LOW, MEDIUM, HIGH)
        payload: Burst size in bytes
        verbose: Print detailed results

    Returns:
        dict: Contains read/write configs, performance objects, and dataframes
    """
    # Get mode configuration
    if mode == PerformanceMode.LOW:
        mode_cfg = LOW_PERF_CONFIG
    elif mode == PerformanceMode.MEDIUM:
        mode_cfg = MEDIUM_PERF_CONFIG
    else:
        mode_cfg = HIGH_PERF_CONFIG

    # Create configurations
    dma_config = create_mode_configs(mode, payload)

    # Create performance analyzers
    dma_perf = StreamDMAPerformance(dma_config)

    # Generate tables
    read_df = dma_perf.read_perf.generate_performance_table(max_channels=8)
    write_df = dma_perf.write_perf.generate_performance_table(max_channels=8)
    dma_df = dma_perf.generate_dma_table(max_channels=8)

    if verbose:
        print("="*80)
        print(f"  {mode.value} PERFORMANCE MODE")
        print(f"  {mode_cfg['use_case']}")
        print("="*80)

        print("\nConfiguration:")
        print(f"  Payload:              {payload} bytes")
        print(f"  Burst Length:         {payload / 64:.0f} beats")
        print(f"\n  Read Engine:")
        print(f"    Max Burst Length:   {mode_cfg['max_burst_len_read']} beats")
        print(f"    Max Outstanding:    {mode_cfg['max_outstanding_read']} transactions")
        print(f"    Pipeline Depth:     {mode_cfg['pipeline_depth']}")
        print(f"\n  Write Engine:")
        print(f"    Max Burst Length:   {mode_cfg['max_burst_len_write']} beats")
        print(f"    Max Outstanding:    {mode_cfg['max_outstanding_write']} transactions")
        print(f"    Pipeline Depth:     {mode_cfg['pipeline_depth']}")

        # Single channel performance
        read_1ch = dma_perf.read_perf.calculate_channel_bandwidth(1)
        write_1ch = dma_perf.write_perf.calculate_channel_bandwidth(1)

        print(f"\nSingle Channel Performance:")
        print(f"  Read Path:")
        print(f"    Bandwidth:          {read_1ch['B_channel']:.3f} GB/s")
        print(f"    Cycles per burst:   {read_1ch['cycles_per_burst']:.0f}")
        print(f"    Limited by:         {read_1ch['limited_by']}")
        print(f"\n  Write Path:")
        print(f"    Bandwidth:          {write_1ch['B_channel']:.3f} GB/s")
        print(f"    Cycles per burst:   {write_1ch['cycles_per_burst']:.0f}")
        print(f"    Limited by:         {write_1ch['limited_by']}")

        # 8 channel performance
        read_8ch = dma_perf.read_perf.calculate_channel_bandwidth(8)
        write_8ch = dma_perf.write_perf.calculate_channel_bandwidth(8)
        dma_8ch = dma_perf.calculate_dma_bandwidth(8)

        print(f"\n8 Channel Performance:")
        print(f"  Read Path:")
        print(f"    Total Bandwidth:    {read_8ch['total_bw']:.3f} GB/s")
        print(f"    Efficiency:         {read_8ch['efficiency']:.1f}% of AXI peak")
        print(f"    Limited by:         {read_8ch['limited_by']}")
        print(f"\n  Write Path:")
        print(f"    Total Bandwidth:    {write_8ch['total_bw']:.3f} GB/s")
        print(f"    Efficiency:         {write_8ch['efficiency']:.1f}% of AXI peak")
        print(f"    Limited by:         {write_8ch['limited_by']}")
        print(f"\n  DMA Throughput:")
        print(f"    End-to-End:         {dma_8ch['dma_throughput']:.3f} GB/s")
        print(f"    Bottleneck:         {dma_8ch['bottleneck']}")

        print("="*80 + "\n")

    return {
        'mode': mode,
        'mode_config': mode_cfg,
        'dma_config': dma_config,
        'dma_performance': dma_perf,
        'read_df': read_df,
        'write_df': write_df,
        'dma_df': dma_df
    }


def compare_all_modes(payload: int = 1024, verbose: bool = True, include_perfect: bool = False):
    """
    Compare performance across all modes.

    Args:
        payload: Burst size in bytes
        verbose: Print detailed comparison
        include_perfect: Include PERFECT mode in comparison

    Returns:
        dict: Results for each mode
    """
    results = {}

    modes = [PerformanceMode.LOW, PerformanceMode.MEDIUM, PerformanceMode.HIGH]
    if include_perfect:
        modes.append(PerformanceMode.PERFECT)

    for mode in modes:
        results[mode.value] = analyze_single_mode(mode, payload, verbose=False)

    if verbose:
        print("="*80)
        print("  PERFORMANCE MODE COMPARISON")
        print(f"  Payload: {payload} bytes")
        print("="*80)

        print(f"\n{'Mode':<10} {'Read BW':<12} {'Write BW':<12} {'DMA Thru':<12} {'Bottleneck':<15}")
        print(f"{'':10} {'(GB/s)':<12} {'(GB/s)':<12} {'(GB/s)':<12} {'':15}")
        print("-" * 70)

        for mode in results.keys():
            dma_8ch = results[mode]['dma_performance'].calculate_dma_bandwidth(8)
            print(f"{mode:<10} {dma_8ch['read_bw']:6.3f}      "
                  f"{dma_8ch['write_bw']:6.3f}      "
                  f"{dma_8ch['dma_throughput']:6.3f}      "
                  f"{dma_8ch['bottleneck']}")

        print("\nKey Insights:")
        print("  - Low mode: Sequential operation, limited by timing")
        print("  - Medium mode: Basic pipelining, improved throughput")
        print("  - High mode: Full pipelining, approaches AXI peak")
        if include_perfect:
            print("  - Perfect mode: Theoretical maximum (requires 16x more SRAM)")
        print("  - Read and write paths independent (decoupled by SRAM)")
        print("="*80 + "\n")

    return results


def payload_sweep_analysis(mode: PerformanceMode, verbose: bool = True):
    """
    Analyze performance across different payload sizes for given mode.

    Args:
        mode: Performance mode to analyze
        verbose: Print results

    Returns:
        dict: Results for each payload size
    """
    dma_config = create_mode_configs(mode, payload=1024)  # Default, will override
    dma_perf = StreamDMAPerformance(dma_config)

    # Run sweep for read and write paths
    read_results = dma_perf.read_perf.compare_payloads(
        max_channels=8,
        payloads=DEFAULT_PAYLOAD_OPTIONS
    )
    write_results = dma_perf.write_perf.compare_payloads(
        max_channels=8,
        payloads=DEFAULT_PAYLOAD_OPTIONS
    )

    if verbose:
        print("="*80)
        print(f"  PAYLOAD SIZE SWEEP - {mode.value} MODE")
        print("="*80)

        print(f"\n{'Payload':<12} {'Burst':<10} {'Read 1ch':<12} {'Write 1ch':<12} {'Read 8ch':<12} {'Write 8ch':<12}")
        print(f"{'':12} {'Beats':<10} {'(GB/s)':<12} {'(GB/s)':<12} {'(GB/s)':<12} {'(GB/s)':<12}")
        print("-" * 80)

        for payload in DEFAULT_PAYLOAD_OPTIONS:
            burst_len = payload / 64
            read_1ch = read_results[payload].iloc[0]['BW_per_Channel_GBps']
            write_1ch = write_results[payload].iloc[0]['BW_per_Channel_GBps']
            read_8ch = read_results[payload].iloc[7]['Total_BW_GBps']
            write_8ch = write_results[payload].iloc[7]['Total_BW_GBps']

            print(f"{payload:5d}B      {burst_len:3.0f}       "
                  f"{read_1ch:6.3f}      "
                  f"{write_1ch:6.3f}      "
                  f"{read_8ch:6.3f}      "
                  f"{write_8ch:6.3f}")

        print("\nKey Insights:")
        print("  - Larger payloads reduce per-burst overhead")
        print("  - Effective burst length limited by max_burst_len")
        print(f"  - {mode.value} mode caps burst at {dma_config.read_config.max_burst_len} (read) / "
              f"{dma_config.write_config.max_burst_len} (write) beats")
        print("="*80 + "\n")

    return {
        'read': read_results,
        'write': write_results
    }


def run_full_analysis(include_perfect: bool = False):
    """Run complete analysis with all modes and configurations.

    Args:
        include_perfect: Include PERFECT mode in analysis
    """
    print("\n" + "="*80)
    print("  STREAM DMA PERFORMANCE ANALYSIS")
    print("  Memory-to-Memory DMA with Low/Medium/High Modes")
    if include_perfect:
        print("  (Including PERFECT mode - theoretical maximum)")
    print("="*80 + "\n")

    # Show default configuration
    print("1. DEFAULT CONFIGURATION")
    print("-" * 80)
    show_defaults()

    # Analyze each mode
    print("\n2. INDIVIDUAL MODE ANALYSIS (1KB payload)")
    print("-" * 80)
    low_results = analyze_single_mode(PerformanceMode.LOW, payload=1024, verbose=True)
    medium_results = analyze_single_mode(PerformanceMode.MEDIUM, payload=1024, verbose=True)
    high_results = analyze_single_mode(PerformanceMode.HIGH, payload=1024, verbose=True)

    if include_perfect:
        perfect_results = analyze_single_mode(PerformanceMode.PERFECT, payload=1024, verbose=True)

    # Compare modes
    print("\n3. MODE COMPARISON")
    print("-" * 80)
    mode_comparison = compare_all_modes(payload=1024, verbose=True, include_perfect=include_perfect)

    # Payload sweep for each mode
    print("\n4. PAYLOAD SIZE ANALYSIS")
    print("-" * 80)
    low_sweep = payload_sweep_analysis(PerformanceMode.LOW, verbose=True)
    medium_sweep = payload_sweep_analysis(PerformanceMode.MEDIUM, verbose=True)
    high_sweep = payload_sweep_analysis(PerformanceMode.HIGH, verbose=True)

    if include_perfect:
        perfect_sweep = payload_sweep_analysis(PerformanceMode.PERFECT, verbose=True)

    # Summary
    print("\n" + "="*80)
    print("  SUMMARY")
    print("="*80)

    summary_data = []
    for mode in mode_comparison.keys():
        dma_8ch = mode_comparison[mode]['dma_performance'].calculate_dma_bandwidth(8)
        summary_data.append({
            'Mode': mode,
            'Read_BW': dma_8ch['read_bw'],
            'Write_BW': dma_8ch['write_bw'],
            'DMA_Throughput': dma_8ch['dma_throughput'],
            'Bottleneck': dma_8ch['bottleneck']
        })

    summary_df = pd.DataFrame(summary_data)
    print("\nEnd-to-End DMA Throughput (8 channels, 1KB payload):")
    print(summary_df.to_string(index=False))

    print("\nRecommendations:")
    print("  - Tutorial/Learning:      Use LOW mode (simple, easy to understand)")
    print("  - Typical FPGA:           Use MEDIUM mode (balanced performance/area)")
    print("  - High-Performance ASIC:  Use HIGH mode (maximum throughput)")
    if include_perfect:
        print("  - PERFECT mode:           Theoretical only (16x more SRAM, NOT recommended)")
    print("\n" + "="*80 + "\n")

    results = {
        'low': low_results,
        'medium': medium_results,
        'high': high_results,
        'comparison': mode_comparison,
        'sweeps': {
            'low': low_sweep,
            'medium': medium_sweep,
            'high': high_sweep
        }
    }

    if include_perfect:
        results['perfect'] = perfect_results
        results['sweeps']['perfect'] = perfect_sweep

    return results


def generate_plots(results: dict, output_dir: str = "assets"):
    """Generate all visualization plots."""
    try:
        from pyperf import PerformanceGraphs
        import os

        os.makedirs(output_dir, exist_ok=True)
        graphs = PerformanceGraphs()

        peak_bw = results['low']['dma_config'].read_config.Bmax

        # Plot each mode
        for mode_name in ['low', 'medium', 'high']:
            mode_result = results[mode_name]

            # Read path
            graphs.plot_combined(
                mode_result['read_df'],
                peak_bw,
                title=f"{mode_name.upper()} Mode Read Performance",
                save_path=os.path.join(output_dir, f'{mode_name}_read.png')
            )

            # Write path
            graphs.plot_combined(
                mode_result['write_df'],
                peak_bw,
                title=f"{mode_name.upper()} Mode Write Performance",
                save_path=os.path.join(output_dir, f'{mode_name}_write.png')
            )

            # Read vs Write comparison
            graphs.plot_read_write_separate(
                mode_result['read_df'],
                mode_result['write_df'],
                peak_bw,
                title=f"{mode_name.upper()} Mode: Read vs Write",
                save_path=os.path.join(output_dir, f'{mode_name}_comparison.png')
            )

        # Mode comparison
        mode_dma_tables = {
            'LOW': results['comparison']['LOW']['dma_df'],
            'MEDIUM': results['comparison']['MEDIUM']['dma_df'],
            'HIGH': results['comparison']['HIGH']['dma_df']
        }
        graphs.plot_mode_comparison(
            mode_dma_tables,
            peak_bw,
            title="STREAM Performance Mode Comparison",
            save_path=os.path.join(output_dir, 'mode_comparison.png')
        )

        print(f"✓ Plots saved to {output_dir}/")

    except ImportError as e:
        print(f"Could not generate plots: {e}")
        print("Install matplotlib to enable plot generation")


def main():
    parser = argparse.ArgumentParser(description='STREAM DMA Performance Analysis')
    parser.add_argument('--mode', choices=['LOW', 'MEDIUM', 'HIGH', 'PERFECT'],
                       help='Analyze specific mode only')
    parser.add_argument('--payload', type=int, default=1024,
                       help='Payload size in bytes (default: 1024)')
    parser.add_argument('--plots', action='store_true',
                       help='Generate visualization plots')
    parser.add_argument('--output-dir', default='assets',
                       help='Output directory for plots (default: assets)')
    parser.add_argument('--report', action='store_true',
                       help='Generate detailed analysis report')
    parser.add_argument('--report-dir', default='reports',
                       help='Output directory for reports (default: reports)')
    parser.add_argument('--include-perfect', action='store_true',
                       help='Include PERFECT mode in full analysis')

    args = parser.parse_args()

    if args.mode:
        # Analyze single mode
        mode = PerformanceMode[args.mode]
        results = analyze_single_mode(mode, payload=args.payload, verbose=True)
        sweep = payload_sweep_analysis(mode, verbose=True)

        if args.plots:
            print("\nGenerating plots...")
            try:
                from pyperf import PerformanceGraphs
                graphs = PerformanceGraphs()
                peak_bw = results['dma_config'].read_config.Bmax

                os.makedirs(args.output_dir, exist_ok=True)

                graphs.plot_read_write_separate(
                    results['read_df'],
                    results['write_df'],
                    peak_bw,
                    title=f"{args.mode} Mode Performance",
                    show=True,
                    save_path=os.path.join(args.output_dir, f'{args.mode.lower()}_comparison.png')
                )
            except ImportError:
                print("matplotlib not available for plotting")

        if args.report:
            print("\nGenerating detailed report...")
            try:
                from pyperf.reporting import PerformanceReporter
                os.makedirs(args.report_dir, exist_ok=True)

                reporter = PerformanceReporter(args.report_dir)
                report_file = os.path.join(args.report_dir, f'stream_dma_{args.mode.lower()}_report.md')
                reporter.generate_complete_report(mode, payload=args.payload, output_file=report_file)
            except ImportError as e:
                print(f"Could not generate report: {e}")

    else:
        # Run full analysis
        results = run_full_analysis(include_perfect=args.include_perfect)

        if args.plots:
            print("\nGenerating plots...")
            generate_plots(results, args.output_dir)

        if args.report:
            print("\nGenerating detailed reports for all modes...")
            try:
                from pyperf.reporting import PerformanceReporter
                os.makedirs(args.report_dir, exist_ok=True)

                reporter = PerformanceReporter(args.report_dir)
                modes_to_report = [PerformanceMode.LOW, PerformanceMode.MEDIUM, PerformanceMode.HIGH]
                if args.include_perfect:
                    modes_to_report.append(PerformanceMode.PERFECT)

                for mode in modes_to_report:
                    report_file = os.path.join(args.report_dir, f'stream_dma_{mode.value.lower()}_report.md')
                    reporter.generate_complete_report(mode, payload=1024, output_file=report_file)

                print(f"✓ All reports saved to {args.report_dir}/")
            except ImportError as e:
                print(f"Could not generate reports: {e}")


if __name__ == "__main__":
    main()
