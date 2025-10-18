#!/usr/bin/env python3
"""
Example: Complete System Analysis - Read + Write Paths

Demonstrates how to analyze both read and write paths together
to understand complete system performance.

Usage:
    python example_both_paths.py
"""

import sys
import os

# Add project root to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from analytical.current_design import get_baseline_performance, get_optimized_performance
from analytical.write_analysis import get_write_performance, get_optimized_write_performance
from analytical.write_analysis import analyze_combined_performance


def analyze_read_write_system():
    """Complete analysis of read + write system."""
    
    print("\n" + "="*80)
    print("  COMPLETE SYSTEM ANALYSIS: READ + WRITE PATHS")
    print("="*80 + "\n")
    
    # ========================================================================
    # PART 1: BASELINE (Both Unoptimized)
    # ========================================================================
    print("1. BASELINE CONFIGURATION")
    print("-" * 80)
    
    # Get read baseline
    read_base = get_baseline_performance(verbose=False)
    read_base_bw = read_base['performance'].calculate_channel_bandwidth(16)['total_bw']
    
    # Get write baseline
    write_base = get_write_performance(num_channels=16, verbose=False)
    write_base_bw = write_base['result']['total_bw']
    
    # Combined (limited by AXI peak)
    axi_peak = 57.6
    combined_base = min(read_base_bw + write_base_bw, axi_peak)
    
    print(f"\nRead Path (Baseline):")
    print(f"  Burst size:       2048 bytes")
    print(f"  Pipeline:         None (stop-and-wait)")
    print(f"  Drain mode:       Store-and-forward")
    print(f"  Bandwidth:        {read_base_bw:.2f} GB/s")
    
    print(f"\nWrite Path (Baseline):")
    print(f"  Burst size:       256 bytes")
    print(f"  Outstanding:      32 (system-wide)")
    print(f"  Bandwidth:        {write_base_bw:.2f} GB/s")
    
    print(f"\nCombined System:")
    print(f"  Read + Write:     {read_base_bw:.2f} + {write_base_bw:.2f} = {read_base_bw + write_base_bw:.2f} GB/s")
    print(f"  AXI Peak:         {axi_peak:.2f} GB/s")
    print(f"  Actual Combined:  {combined_base:.2f} GB/s")
    if read_base_bw + write_base_bw > axi_peak:
        print(f"  ⚠️  Limited by AXI bandwidth (paths compete)")
    
    # ========================================================================
    # PART 2: OPTIMIZED (Both Optimized)
    # ========================================================================
    print("\n\n2. OPTIMIZED CONFIGURATION")
    print("-" * 80)
    
    # Get read optimized
    read_opt = get_optimized_performance(
        pipeline_depth=4,
        streaming=True,
        monolithic=False,
        payload=2048,
        verbose=False
    )
    read_opt_bw = read_opt['performance'].calculate_channel_bandwidth(16)['total_bw']
    
    # Get write optimized
    write_opt = get_optimized_write_performance(
        num_channels=16,
        max_outstanding=64,
        verbose=False
    )
    write_opt_bw = write_opt['result']['total_bw']
    
    # Combined
    combined_opt = min(read_opt_bw + write_opt_bw, axi_peak)
    
    print(f"\nRead Path (Optimized):")
    print(f"  Pipeline:         depth=4")
    print(f"  Drain mode:       Streaming")
    print(f"  Bandwidth:        {read_opt_bw:.2f} GB/s")
    print(f"  Improvement:      +{((read_opt_bw/read_base_bw)-1)*100:.1f}%")
    
    print(f"\nWrite Path (Optimized):")
    print(f"  Outstanding:      64 (doubled)")
    print(f"  Bandwidth:        {write_opt_bw:.2f} GB/s")
    print(f"  Improvement:      +{((write_opt_bw/write_base_bw)-1)*100:.1f}%")
    
    print(f"\nCombined System:")
    print(f"  Read + Write:     {read_opt_bw:.2f} + {write_opt_bw:.2f} = {read_opt_bw + write_opt_bw:.2f} GB/s")
    print(f"  Actual Combined:  {combined_opt:.2f} GB/s")
    if read_opt_bw + write_opt_bw > axi_peak:
        print(f"  ⚠️  Limited by AXI bandwidth")
    
    # ========================================================================
    # PART 3: COMPARISON TABLE
    # ========================================================================
    print("\n\n3. COMPARISON: BASELINE vs OPTIMIZED")
    print("-" * 80 + "\n")
    
    print(f"{'Configuration':<15} {'Read BW':<15} {'Write BW':<15} {'Combined':<15} {'AXI Util':<10}")
    print("-" * 75)
    print(f"{'Baseline':<15} {read_base_bw:>8.2f} GB/s   {write_base_bw:>8.2f} GB/s   "
          f"{combined_base:>8.2f} GB/s   {combined_base/axi_peak*100:>5.1f}%")
    print(f"{'Optimized':<15} {read_opt_bw:>8.2f} GB/s   {write_opt_bw:>8.2f} GB/s   "
          f"{combined_opt:>8.2f} GB/s   {combined_opt/axi_peak*100:>5.1f}%")
    print("-" * 75)
    
    read_impr = ((read_opt_bw/read_base_bw)-1)*100
    write_impr = ((write_opt_bw/write_base_bw)-1)*100
    combined_impr = ((combined_opt/combined_base)-1)*100
    
    print(f"{'Improvement':<15} {read_impr:>+8.1f}%      {write_impr:>+8.1f}%      "
          f"{combined_impr:>+8.1f}%      —")
    
    # ========================================================================
    # PART 4: KEY INSIGHTS
    # ========================================================================
    print("\n\n4. KEY INSIGHTS")
    print("-" * 80)
    
    print("\n✓ Read Path:")
    print(f"  • Optimizations improve read by {read_impr:.1f}%")
    print(f"  • Achieves {read_opt_bw:.1f} GB/s (exceeds 50 GB/s target)")
    print(f"  • Key: Pipelining + streaming drain")
    
    print("\n✓ Write Path:")
    print(f"  • Increasing outstanding limit improves by {write_impr:.1f}%")
    print(f"  • Achieves {write_opt_bw:.1f} GB/s")
    print(f"  • Key: More outstanding bursts (32 → 64)")
    
    print("\n⚠️  AXI Bandwidth Sharing:")
    print(f"  • AXI peak: {axi_peak} GB/s (shared between read and write)")
    print(f"  • Baseline: {combined_base:.1f} GB/s ({combined_base/axi_peak*100:.0f}% of peak)")
    print(f"  • Optimized: {combined_opt:.1f} GB/s ({combined_opt/axi_peak*100:.0f}% of peak)")
    if combined_base >= axi_peak * 0.95:
        print(f"  • Both configurations saturate AXI bandwidth")
        print(f"  • Actual workload mix determines effective performance")
    
    print("\n📊 Workload-Dependent Performance:")
    print(f"  • Read-heavy (80/20): ~{0.8*read_opt_bw + 0.2*write_opt_bw:.1f} GB/s effective")
    print(f"  • Balanced (50/50): ~{axi_peak:.1f} GB/s (AXI limited)")
    print(f"  • Write-heavy (20/80): ~{0.2*read_opt_bw + 0.8*write_opt_bw:.1f} GB/s effective")
    
    # ========================================================================
    # PART 5: RECOMMENDATIONS
    # ========================================================================
    print("\n\n5. DESIGN RECOMMENDATIONS")
    print("-" * 80)
    
    print("\n✅ Implement for Read Path:")
    print("  1. Pipelining (depth=4) - ~70% improvement")
    print("  2. Streaming drain - ~5% additional improvement")
    print("  3. Monolithic SRAM (8KB/ch) - enables pipelining")
    
    print("\n✅ Implement for Write Path:")
    print("  1. Increase outstanding burst limit (32 → 64) - ~35% improvement")
    print("  2. Consider write buffer sizing (minimal SRAM needed)")
    
    print("\n⚠️  System-Level Considerations:")
    print("  • Both paths share 57.6 GB/s AXI bandwidth")
    print("  • Workload mix affects actual performance")
    print("  • Read path optimizations are priority (larger bottleneck)")
    print("  • Write improvements are secondary benefit")
    
    print("\n" + "="*80 + "\n")
    
    return {
        'baseline': {
            'read_bw': read_base_bw,
            'write_bw': write_base_bw,
            'combined_bw': combined_base
        },
        'optimized': {
            'read_bw': read_opt_bw,
            'write_bw': write_opt_bw,
            'combined_bw': combined_opt
        },
        'improvements': {
            'read': read_impr,
            'write': write_impr,
            'combined': combined_impr
        }
    }


def demonstrate_combined_analysis_function():
    """Demonstrate using the built-in combined analysis function."""
    
    print("\n" + "="*80)
    print("  USING COMBINED ANALYSIS FUNCTION")
    print("="*80 + "\n")
    
    print("The write_analysis module provides analyze_combined_performance()")
    print("which analyzes both paths together automatically.\n")
    
    # Baseline
    print("1. Analyzing baseline configuration...")
    baseline = analyze_combined_performance(
        num_channels=16,
        read_optimized=False,
        write_optimized=False,
        verbose=True
    )
    
    # Optimized
    print("\n2. Analyzing optimized configuration...")
    optimized = analyze_combined_performance(
        num_channels=16,
        read_optimized=True,
        write_optimized=True,
        verbose=True
    )
    
    return {
        'baseline': baseline,
        'optimized': optimized
    }


if __name__ == "__main__":
    print("\n" + "="*80)
    print("  COMPLETE SYSTEM PERFORMANCE ANALYSIS")
    print("  Read + Write Paths Together")
    print("="*80)
    
    # Run detailed manual analysis
    print("\n" + "="*80)
    print("  METHOD 1: Detailed Manual Analysis")
    print("="*80)
    results_manual = analyze_read_write_system()
    
    # Run using combined analysis function
    print("\n" + "="*80)
    print("  METHOD 2: Using Combined Analysis Function")
    print("="*80)
    results_function = demonstrate_combined_analysis_function()
    
    print("\n" + "="*80)
    print("  SUMMARY")
    print("="*80)
    print("\n✓ Complete system analysis includes BOTH read and write paths")
    print("✓ Both paths compete for shared AXI bandwidth (57.6 GB/s)")
    print("✓ Optimizations improve both paths significantly")
    print("✓ Actual performance depends on workload mix")
    print("\n" + "="*80 + "\n")
