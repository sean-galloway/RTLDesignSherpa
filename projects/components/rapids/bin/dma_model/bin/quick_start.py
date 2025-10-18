# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: quick_start
# Purpose: Quick Start Examples for AXI4 Performance Modeling
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Quick Start Examples for AXI4 Performance Modeling

Run specific examples or all at once. All plots saved to 'assets/' directory.

Usage:
    python quick_start.py 1        # Run example 1
    python quick_start.py all      # Run all examples
"""

import sys
import os


def example_1_analytical_baseline():
    """Example 1: Analytical model baseline."""
    print("\n" + "="*80)
    print("  EXAMPLE 1: Analytical Model - Baseline Performance")
    print("="*80 + "\n")
    
    from analytical import get_baseline_performance
    
    result = get_baseline_performance(verbose=True)
    
    # Show 16-channel performance
    perf_16ch = result['performance'].calculate_channel_bandwidth(16)
    print(f"✓ 16-channel aggregate: {perf_16ch['total_bw']:.2f} GB/s")
    
    return result


def example_2_simpy_baseline():
    """Example 2: SimPy simulation baseline."""
    print("\n" + "="*80)
    print("  EXAMPLE 2: SimPy Simulation - Baseline Performance")
    print("="*80 + "\n")
    
    from simpy_model import run_baseline_simulation
    
    result = run_baseline_simulation(
        num_channels=16,
        simulation_time=100000,
        payload=2048,
        verbose=True
    )
    
    print(f"✓ SimPy aggregate: {result['aggregate_bandwidth']:.2f} GB/s")
    
    return result


def example_3_compare_baseline_optimized():
    """Example 3: Compare baseline vs optimized."""
    print("\n" + "="*80)
    print("  EXAMPLE 3: Baseline vs Optimized Comparison")
    print("="*80 + "\n")
    
    from analytical import get_baseline_performance, get_optimized_performance
    
    print("Running baseline...")
    baseline = get_baseline_performance(verbose=False)
    baseline_bw = baseline['performance'].calculate_channel_bandwidth(16)['total_bw']
    
    print("Running optimized (pipeline + streaming)...")
    optimized = get_optimized_performance(
        pipeline_depth=4,
        streaming=True,
        verbose=False
    )
    optimized_bw = optimized['performance'].calculate_channel_bandwidth(16)['total_bw']
    
    improvement = ((optimized_bw / baseline_bw) - 1) * 100
    
    print(f"\nResults:")
    print(f"  Baseline:    {baseline_bw:.2f} GB/s")
    print(f"  Optimized:   {optimized_bw:.2f} GB/s")
    print(f"  Improvement: +{improvement:.1f}%")
    
    target_met = "✓" if optimized_bw >= 50 else "✗"
    print(f"  Meets 50+ GB/s target: {target_met}")
    
    return {'baseline': baseline, 'optimized': optimized}


def example_4_optimization_sequence():
    """Example 4: Incremental optimization sequence."""
    print("\n" + "="*80)
    print("  EXAMPLE 4: Optimization Sequence (SimPy)")
    print("="*80 + "\n")
    
    from simpy_model import run_optimization_sequence
    
    results = run_optimization_sequence(
        num_channels=16,
        simulation_time=100000,
        payload=2048,
        verbose=False
    )
    
    print("Optimization steps:")
    for name, result in results.items():
        print(f"  {name:30s}: {result['aggregate_bandwidth']:.2f} GB/s")
    
    return results


def example_5_validate_models():
    """Example 5: Validate analytical vs SimPy."""
    print("\n" + "="*80)
    print("  EXAMPLE 5: Model Validation")
    print("="*80 + "\n")
    
    from simpy_model.validate import validate_all_configurations, generate_validation_report
    
    print("Running validation suite...")
    results = validate_all_configurations(
        num_channels=16,
        simulation_time=100000,
        payload=2048,
        verbose=False
    )
    
    report = generate_validation_report(results, save_csv=True)
    
    passed = sum(1 for r in results.values() if r.within_tolerance)
    total = len(results)
    print(f"\n✓ Validation: {passed}/{total} configurations passed (<5% difference)")
    
    return results


def example_6_generate_plots():
    """Example 6: Generate comparison plots."""
    print("\n" + "="*80)
    print("  EXAMPLE 6: Generate Comparison Plots")
    print("="*80 + "\n")
    
    try:
        import matplotlib.pyplot as plt
        from pyperf import PerformanceGraphs
        from analytical import get_baseline_performance, get_optimized_performance
        
        # Create assets directory if needed
        assets_dir = 'assets'
        if not os.path.exists(assets_dir):
            os.makedirs(assets_dir)
            print(f"Created directory: {assets_dir}/")
        
        # Get data
        baseline = get_baseline_performance(verbose=False)
        optimized = get_optimized_performance(
            pipeline_depth=4,
            streaming=True,
            verbose=False
        )
        
        # Create graphs
        graphs = PerformanceGraphs()
        
        # Plot baseline
        print("Generating baseline plot...")
        graphs.plot_combined(
            baseline['dataframe'],
            baseline['config'].Bmax,
            title="Baseline Performance (Current Design)",
            show=False
        )
        baseline_path = os.path.join(assets_dir, 'example_baseline.png')
        plt.savefig(baseline_path, dpi=150, bbox_inches='tight')
        print(f"  ✓ Saved: {baseline_path}")
        plt.close()
        
        # Plot optimized
        print("Generating optimized plot...")
        graphs.plot_combined(
            optimized['dataframe'],
            optimized['config'].Bmax,
            title="Optimized Performance (Pipeline + Streaming)",
            show=False
        )
        optimized_path = os.path.join(assets_dir, 'example_optimized.png')
        plt.savefig(optimized_path, dpi=150, bbox_inches='tight')
        print(f"  ✓ Saved: {optimized_path}")
        plt.close()
        
        # Comparison plot
        print("Generating comparison plot...")
        graphs.plot_comparison(
            [baseline['dataframe'], optimized['dataframe']],
            ['Baseline', 'Optimized'],
            baseline['config'].Bmax,
            title="Baseline vs Optimized Comparison",
            show=False
        )
        comparison_path = os.path.join(assets_dir, 'example_comparison.png')
        plt.savefig(comparison_path, dpi=150, bbox_inches='tight')
        print(f"  ✓ Saved: {comparison_path}")
        plt.close()
        
        print(f"\n✓ All plots generated successfully in '{assets_dir}/'!")
        
        return True
        
    except ImportError:
        print("✗ Matplotlib not available. Cannot generate plots.")
        print("  Install with: pip install matplotlib")
        return False
    except Exception as e:
        print(f"✗ Error generating plots: {e}")
        return False


def example_7_sram_analysis():
    """Example 7: SRAM sizing analysis."""
    print("\n" + "="*80)
    print("  EXAMPLE 7: SRAM Sizing Analysis")
    print("="*80 + "\n")
    
    try:
        from analytical.sram_analysis import (
            compare_sram_modes,
            find_optimal_sram_size,
            analyze_payload_vs_sram
        )
        
        # 1. Compare ping-pong vs monolithic for 2KB
        print("1. Comparing SRAM modes for 2KB payload...")
        comparison = compare_sram_modes(
            payload=2048,
            pipeline_depth=4,
            num_channels=16,
            verbose=True
        )
        
        # 2. Find optimal SRAM for target bandwidth
        print("\n2. Finding optimal SRAM for 50 GB/s target...")
        optimal = find_optimal_sram_size(
            payload=2048,
            target_bandwidth=50.0,
            num_channels=16,
            streaming=True,
            verbose=True
        )
        
        # 3. Full payload analysis
        print("\n3. Running full payload vs SRAM analysis...")
        df = analyze_payload_vs_sram(
            payloads=[256, 512, 1024, 2048],
            pipeline_depths=[1, 2, 4, 8],
            num_channels=16,
            streaming=True,
            verbose=False
        )
        
        print(f"\n✓ Analysis complete. Data saved to sram_payload_analysis.csv")
        print(f"✓ Recommendations saved to sram_recommendations.csv")
        
        # Generate visualizations if matplotlib available
        try:
            from analytical.sram_visualization import plot_all_sram_analysis
            print("\n4. Generating SRAM visualization plots...")
            plot_all_sram_analysis(df)  # Saves to assets/ by default
        except ImportError:
            print("\nSkipping visualizations (matplotlib not available)")
        
        return {'comparison': comparison, 'optimal': optimal, 'analysis': df}
        
    except Exception as e:
        print(f"✗ Error in SRAM analysis: {e}")
        return None


def print_usage():
    """Print usage instructions."""
    print("\nUsage: python quick_start.py <example_number>")
    print("\nAvailable examples:")
    print("  1 - Analytical baseline")
    print("  2 - SimPy baseline")
    print("  3 - Baseline vs optimized")
    print("  4 - Optimization sequence")
    print("  5 - Model validation")
    print("  6 - Generate plots")
    print("  7 - SRAM analysis")
    print("  all - Run all examples")
    print("\nExamples:")
    print("  python quick_start.py 1")
    print("  python quick_start.py 3")
    print("  python quick_start.py 7")
    print("  python quick_start.py all")
    print()


def run_all_examples():
    """Run all examples in sequence."""
    print("\n" + "="*80)
    print("  RUNNING ALL EXAMPLES")
    print("="*80)
    
    examples = [
        ("Example 1: Analytical Baseline", example_1_analytical_baseline),
        ("Example 2: SimPy Baseline", example_2_simpy_baseline),
        ("Example 3: Baseline vs Optimized", example_3_compare_baseline_optimized),
        ("Example 4: Optimization Sequence", example_4_optimization_sequence),
        ("Example 5: Model Validation", example_5_validate_models),
        ("Example 6: Generate Plots", example_6_generate_plots),
        ("Example 7: SRAM Analysis", example_7_sram_analysis),
    ]
    
    results = {}
    
    for name, func in examples:
        print(f"\n{'='*80}")
        print(f"  {name}")
        print(f"{'='*80}")
        try:
            result = func()
            results[name] = result
            print(f"\n✓ {name} completed successfully")
        except Exception as e:
            print(f"\n✗ Error in {name}: {e}")
            import traceback
            traceback.print_exc()
    
    print("\n" + "="*80)
    print("  ALL EXAMPLES COMPLETE")
    print("="*80)
    print("\nCheck the 'assets/' directory for all generated plots!")
    print("="*80 + "\n")
    
    return results


def main():
    """Main entry point."""
    if len(sys.argv) < 2:
        print_usage()
        return 1
    
    example = sys.argv[1].lower()
    
    examples = {
        '1': example_1_analytical_baseline,
        '2': example_2_simpy_baseline,
        '3': example_3_compare_baseline_optimized,
        '4': example_4_optimization_sequence,
        '5': example_5_validate_models,
        '6': example_6_generate_plots,
        '7': example_7_sram_analysis,
        'all': run_all_examples,
    }
    
    if example not in examples:
        print(f"Error: Unknown example '{example}'")
        print_usage()
        return 1
    
    try:
        examples[example]()
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
