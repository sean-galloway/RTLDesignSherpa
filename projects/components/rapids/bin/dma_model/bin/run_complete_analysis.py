# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: run_complete_analysis
# Purpose: Complete Analysis Runner
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Complete Analysis Runner

Runs full suite of AXI4 performance analysis including:
- Analytical model
- SimPy simulation
- Model validation
- Detailed comparison
- SRAM sizing analysis

All plots saved to 'assets/' directory.

Usage:
    python run_complete_analysis.py              # Full analysis
    python run_complete_analysis.py --quick       # Quick mode
    python run_complete_analysis.py --no-plots    # Skip plots
    python run_complete_analysis.py --no-sram     # Skip SRAM analysis
"""

import sys
import os
import argparse


def print_header(title: str):
    """Print section header."""
    print("\n" + "="*80)
    print(f"  {title}")
    print("="*80 + "\n")


def run_complete_analysis(quick_mode: bool = False,
                         generate_plots: bool = True,
                         run_sram: bool = True):
    """
    Run complete performance analysis suite.
    
    Args:
        quick_mode: Use shorter simulation times
        generate_plots: Generate visualization plots
        run_sram: Run SRAM sizing analysis
    """
    # Create assets directory if needed
    assets_dir = 'assets'
    if generate_plots and not os.path.exists(assets_dir):
        os.makedirs(assets_dir)
        print(f"Created directory: {assets_dir}/")
    
    # Simulation parameters
    simulation_time = 50000 if quick_mode else 100000
    
    print("\n" + "="*80)
    print("  AXI4 PERFORMANCE MODELING - COMPLETE ANALYSIS")
    print("="*80)
    
    if quick_mode:
        print("\nMode: QUICK (shorter simulation times)")
    else:
        print("\nMode: FULL (comprehensive analysis)")
    
    print(f"Simulation time: {simulation_time:,} cycles")
    print(f"Generate plots: {'YES' if generate_plots else 'NO'}")
    print(f"SRAM analysis: {'YES' if run_sram else 'NO'}")
    
    # ========================================================================
    # PART 1: ANALYTICAL MODEL
    # ========================================================================
    print_header("PART 1: ANALYTICAL MODEL")
    
    from analytical import (
        get_baseline_performance,
        get_optimized_performance,
        compare_all_payloads
    )
    
    print("1a. Baseline Performance (Read Path)")
    baseline_analytical = get_baseline_performance(verbose=True)
    
    print("\n1b. Optimized Performance (Read Path)")
    optimized_analytical = get_optimized_performance(
        pipeline_depth=4,
        streaming=True,
        verbose=True
    )
    
    print("\n1c. Payload Size Comparison")
    payload_comparison = compare_all_payloads(verbose=True)
    
    # ========================================================================
    # PART 2: SIMPY SIMULATION
    # ========================================================================
    print_header("PART 2: SIMPY DISCRETE-EVENT SIMULATION")
    
    from simpy_model import run_optimization_sequence
    
    print("Running optimization sequence (7 steps):")
    print("  1. Baseline (no pipelining, store-and-forward)")
    print("  2. Pipeline depth=2")
    print("  3. Pipeline depth=4")
    print("  4. Streaming drain only")
    print("  5. Monolithic SRAM only")
    print("  6. Pipeline + Streaming")
    print("  7. Full optimization")
    print()
    
    optimization_results = run_optimization_sequence(
        num_channels=16,
        simulation_time=simulation_time,
        payload=2048,
        verbose=False
    )
    
    baseline_simpy = optimization_results['baseline']['aggregate_bandwidth']
    optimized_simpy = optimization_results['full_optimization']['aggregate_bandwidth']
    
    print("\n📊 SimPy Results Summary (Read Path):")
    print(f"  Baseline (16 ch):    {baseline_simpy:.2f} GB/s")
    print(f"  Optimized (16 ch):   {optimized_simpy:.2f} GB/s")
    print(f"  Improvement:         +{((optimized_simpy/baseline_simpy)-1)*100:.1f}%")
    
    # ========================================================================
    # PART 3: VALIDATION
    # ========================================================================
    print_header("PART 3: MODEL VALIDATION")
    
    from simpy_model.validate import validate_all_configurations, generate_validation_report
    
    print("Validating SimPy against analytical model...")
    print("Testing multiple configurations for agreement...")
    print()
    
    validation_results = validate_all_configurations(
        num_channels=16,
        simulation_time=simulation_time,
        payload=2048,
        verbose=False
    )
    
    validation_report = generate_validation_report(validation_results, save_csv=True)
    
    # ========================================================================
    # PART 4: DETAILED COMPARISON
    # ========================================================================
    print_header("PART 4: DETAILED COMPARISON & VISUALIZATION")
    
    from simpy_model.compare import run_channel_sweep, create_comparison_table, plot_comparison
    
    print("Running channel sweep for comparison...")
    print("Sweeping 1-32 channels for baseline and optimized configs...")
    print()
    
    if quick_mode:
        max_channels = 16
        sim_time = simulation_time
    else:
        max_channels = 32
        sim_time = simulation_time
    
    sweep_results = run_channel_sweep(
        max_channels=max_channels,
        simulation_time=sim_time,
        payload=2048,
        verbose=True
    )
    
    # Create comparison table
    comparison_table = create_comparison_table(sweep_results)
    print("\n📊 Channel Sweep Comparison:")
    print(comparison_table.to_string(index=False))
    print()
    
    # Save table
    try:
        comparison_table.to_csv('model_comparison.csv', index=False)
        print("✓ Saved: model_comparison.csv")
    except Exception as e:
        print(f"✗ Could not save comparison table: {e}")
    
    # Generate plots (saved to assets/)
    if generate_plots:
        print(f"\nGenerating comparison plots to '{assets_dir}/'...")
        try:
            plot_comparison(sweep_results, save_plots=True, show_plots=False)
            print("✓ Plots generated successfully")
        except Exception as e:
            print(f"✗ Could not generate plots: {e}")
    else:
        print("\nSkipping plot generation (--no-plots)")
    
    # ========================================================================
    # PART 5: SRAM SIZING ANALYSIS
    # ========================================================================
    if run_sram:
        print_header("PART 5: SRAM SIZING ANALYSIS")
        
        try:
            from analytical.sram_analysis import (
                analyze_payload_vs_sram,
                find_optimal_sram_size,
                generate_sram_recommendations
            )
            
            print("Running comprehensive SRAM analysis...")
            print("  - Analyzing payloads: 256B, 512B, 1KB, 2KB")
            print("  - Pipeline depths: 1, 2, 4, 8")
            print("  - Comparing ping-pong vs monolithic modes")
            print()
            
            sram_df = analyze_payload_vs_sram(
                payloads=[256, 512, 1024, 2048],
                pipeline_depths=[1, 2, 4, 8],
                num_channels=16,
                streaming=True,
                verbose=False
            )
            
            print("✓ SRAM analysis complete")
            print("✓ Saved: sram_payload_analysis.csv")
            
            # Find optimal configuration
            print("\nFinding optimal SRAM configuration for 50 GB/s target...")
            optimal_sram = find_optimal_sram_size(
                payload=2048,
                target_bandwidth=50.0,
                num_channels=16,
                streaming=True,
                verbose=True
            )
            
            # Generate recommendations
            recommendations = generate_sram_recommendations(sram_df, save_csv=True)
            print("✓ Saved: sram_recommendations.csv")
            
            # Generate SRAM visualizations
            if generate_plots:
                print(f"\nGenerating SRAM plots to '{assets_dir}/'...")
                try:
                    from analytical.sram_visualization import plot_all_sram_analysis
                    plot_all_sram_analysis(sram_df, output_dir=assets_dir)
                except Exception as e:
                    print(f"✗ Could not generate SRAM plots: {e}")
            
            sram_results = True
            
            # Determine best configuration
            best_config = None
            best_mode = None
            for mode in ['pingpong', 'monolithic']:
                if optimal_sram[mode]['achievable']:
                    if best_config is None or optimal_sram[mode]['total_sram_kb'] < best_config['total_sram_kb']:
                        best_config = optimal_sram[mode]
                        best_mode = mode.title()
            
        except Exception as e:
            print(f"✗ SRAM analysis failed: {e}")
            sram_results = False
            best_config = None
    else:
        print("\nSkipping SRAM analysis (--no-sram)")
        sram_results = False
        best_config = None
    
    # ========================================================================
    # FINAL SUMMARY
    # ========================================================================
    print_header("ANALYSIS COMPLETE!")
    
    print("📊 KEY RESULTS:")
    print()
    print("Read Path Performance:")
    print(f"  Baseline:      {baseline_simpy:.2f} GB/s")
    print(f"  Optimized:     {optimized_simpy:.2f} GB/s")
    print(f"  Improvement:   +{((optimized_simpy/baseline_simpy)-1)*100:.1f}%")
    target_status = "✓ YES" if optimized_simpy >= 50 else "✗ NO"
    print(f"  Meets 50 GB/s: {target_status}")
    
    print("\nModel Agreement:")
    passed = sum(1 for r in validation_results.values() if r.within_tolerance)
    total = len(validation_results)
    print(f"  Validation:    {passed}/{total} passed (<5% difference)")
    
    print("\n" + "="*80)
    print("  OUTPUT FILES GENERATED")
    print("="*80 + "\n")
    
    files = [
        'optimization_results.csv',
        'validation_report.csv',
        'model_comparison.csv'
    ]
    if sram_results:
        files.extend(['sram_payload_analysis.csv', 'sram_recommendations.csv'])
    
    if generate_plots:
        plot_files = [
            f'{assets_dir}/comparison_baseline.png',
            f'{assets_dir}/comparison_optimized.png'
        ]
        if sram_results:
            plot_files.extend([
                f'{assets_dir}/sram_efficiency.png',
                f'{assets_dir}/sram_comparison_heatmap.png',
                f'{assets_dir}/sram_cost_benefit.png'
            ])
        files.extend(plot_files)
    
    for f in files:
        exists = os.path.exists(f)
        status = "✓" if exists else "✗"
        print(f"   {status} {f}")
    
    print("\n" + "="*80)
    print("  RECOMMENDATIONS")
    print("="*80)
    
    print("\n✅ IMPLEMENT THESE OPTIMIZATIONS:")
    print("\n  Priority 1: Pipelining (depth=4)")
    print("    - Impact: ~70% bandwidth improvement")
    print("    - Allows drain to overlap with next burst fetch")
    print("    - Hides the 512-cycle drain penalty")
    
    print("\n  Priority 2: Streaming Drain")
    print("    - Impact: ~5% additional improvement")
    print("    - Data drains as it arrives (saves 32 cycles)")
    print("    - Complements pipelining well")
    
    if sram_results and best_config:
        print("\n  Priority 3: SRAM Configuration")
        print(f"    - Recommended: {best_mode} SRAM")
        print(f"    - Size: {best_config['sram_per_ch_kb']:.2f} KB per channel")
        print(f"    - Total: {best_config['total_sram_kb']:.2f} KB for 16 channels")
        print(f"    - Achieves: {best_config['bandwidth']:.2f} GB/s")
    
    print("\n" + "="*80)
    print("  NEXT STEPS")
    print("="*80)
    
    print("\n1. Review plots in the 'assets/' directory")
    print("2. Check CSV files for detailed data")
    print("3. Implement priority optimizations in hardware")
    print("4. Verify with hardware simulation/testing")
    
    if generate_plots:
        print(f"\n💡 TIP: All visualization plots are in '{assets_dir}/'")
    
    print("\n" + "="*80 + "\n")


def main():
    """Main entry point with argument parsing."""
    parser = argparse.ArgumentParser(
        description="Run complete AXI4 performance analysis"
    )
    parser.add_argument(
        '--quick',
        action='store_true',
        help='Quick mode (shorter simulation times)'
    )
    parser.add_argument(
        '--no-plots',
        action='store_true',
        help='Skip plot generation'
    )
    parser.add_argument(
        '--no-sram',
        action='store_true',
        help='Skip SRAM sizing analysis'
    )
    
    args = parser.parse_args()
    
    try:
        run_complete_analysis(
            quick_mode=args.quick,
            generate_plots=not args.no_plots,
            run_sram=not args.no_sram
        )
        return 0
    except KeyboardInterrupt:
        print("\n\nInterrupted by user")
        return 1
    except Exception as e:
        print(f"\nError: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
