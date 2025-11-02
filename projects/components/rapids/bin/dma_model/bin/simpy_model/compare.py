# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ComparisonResult
# Purpose: Comparison and Visualization Module
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Comparison and Visualization Module

Compare analytical and SimPy models across different configurations.
All plots are saved to the 'assets/' directory.

Usage:
    from simpy_model.compare import run_channel_sweep, plot_comparison
    
    results = run_channel_sweep(max_channels=32)
    plot_comparison(results, save_plots=True)  # Saves to assets/
"""

import sys
import os
import numpy as np
import pandas as pd
from typing import Dict, List, Optional
from dataclasses import dataclass

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from pyperf import AXIConfig, AXI4Performance
from simpy_model.current_design import run_baseline_simulation, run_optimized_simulation


@dataclass
class ComparisonResult:
    """Results from comparing analytical and SimPy models."""
    name: str
    analytical_df: pd.DataFrame
    simpy_df: pd.DataFrame
    config: AXIConfig


def compare_single_config(num_channels: int = 16,
                         payload: int = 2048,
                         pipeline_depth: int = 1,
                         streaming: bool = False,
                         monolithic: bool = False,
                         simulation_time: int = 100000,
                         verbose: bool = False) -> Dict:
    """
    Compare analytical vs SimPy for a single configuration.
    
    Args:
        num_channels: Number of channels to simulate
        payload: Burst size in bytes
        pipeline_depth: Pipeline depth
        streaming: Enable streaming drain
        monolithic: Use monolithic SRAM
        simulation_time: SimPy simulation time
        verbose: Print results
    
    Returns:
        Dictionary with both model results
    """
    # Analytical model
    sram_mode = "monolithic" if monolithic else "pingpong"
    config = AXIConfig(
        payload=payload,
        pipeline_depth=pipeline_depth,
        pipelining_enabled=(pipeline_depth > 1),
        streaming_drain=streaming,
        sram_mode=sram_mode
    )
    
    perf = AXI4Performance(config)
    analytical_result = perf.calculate_channel_bandwidth(num_channels)
    
    # SimPy simulation
    if pipeline_depth == 1 and not streaming:
        simpy_result = run_baseline_simulation(
            num_channels=num_channels,
            simulation_time=simulation_time,
            payload=payload,
            verbose=False
        )
    else:
        simpy_result = run_optimized_simulation(
            num_channels=num_channels,
            simulation_time=simulation_time,
            payload=payload,
            pipeline_depth=pipeline_depth,
            streaming=streaming,
            monolithic=monolithic,
            verbose=False
        )
    
    # Compare
    analytical_bw = analytical_result['total_bw']
    simpy_bw = simpy_result['aggregate_bandwidth']
    diff_pct = ((simpy_bw - analytical_bw) / analytical_bw) * 100
    
    if verbose:
        print("="*80)
        print("  MODEL COMPARISON")
        print("="*80)
        print(f"\nConfiguration:")
        print(f"  Channels:      {num_channels}")
        print(f"  Payload:       {payload} bytes")
        print(f"  Pipeline:      {pipeline_depth}")
        print(f"  Streaming:     {streaming}")
        print(f"  SRAM:          {sram_mode}")
        
        print(f"\nResults:")
        print(f"  Analytical:    {analytical_bw:.3f} GB/s")
        print(f"  SimPy:         {simpy_bw:.3f} GB/s")
        print(f"  Difference:    {diff_pct:+.2f}%")
        print("="*80 + "\n")
    
    return {
        'config': config,
        'analytical_bw': analytical_bw,
        'simpy_bw': simpy_bw,
        'diff_pct': diff_pct,
        'analytical_result': analytical_result,
        'simpy_result': simpy_result
    }


def run_channel_sweep(max_channels: int = 32,
                     simulation_time: int = 100000,
                     payload: int = 2048,
                     verbose: bool = False) -> Dict:
    """
    Sweep channel count for both baseline and optimized configurations.
    
    Args:
        max_channels: Maximum number of channels to test
        simulation_time: SimPy simulation time
        payload: Burst size
        verbose: Print progress
    
    Returns:
        Dictionary with baseline and optimized results
    """
    if verbose:
        print(f"\nRunning channel sweep (1-{max_channels} channels)...")
    
    # Baseline configuration
    baseline_config = AXIConfig(
        payload=payload,
        pipeline_depth=1,
        pipelining_enabled=False,
        streaming_drain=False,
        sram_mode="pingpong"
    )
    baseline_perf = AXI4Performance(baseline_config)
    baseline_analytical = baseline_perf.generate_performance_table(max_channels)
    
    # Optimized configuration
    optimized_config = AXIConfig(
        payload=payload,
        pipeline_depth=4,
        pipelining_enabled=True,
        streaming_drain=True,
        sram_mode="pingpong"  # or "monolithic" for even better
    )
    optimized_perf = AXI4Performance(optimized_config)
    optimized_analytical = optimized_perf.generate_performance_table(max_channels)
    
    # SimPy simulations at select channel counts
    test_channels = [1, 2, 4, 8, 16, max_channels] if max_channels > 16 else [1, 2, 4, 8, 16]
    
    baseline_simpy_data = []
    optimized_simpy_data = []
    
    for n in test_channels:
        if verbose:
            print(f"  Testing {n} channels...")
        
        # Baseline SimPy
        baseline_sim = run_baseline_simulation(
            num_channels=n,
            simulation_time=simulation_time,
            payload=payload,
            verbose=False
        )
        baseline_simpy_data.append({
            'Channels': n,
            'SimPy_BW': baseline_sim['aggregate_bandwidth']
        })
        
        # Optimized SimPy
        optimized_sim = run_optimized_simulation(
            num_channels=n,
            simulation_time=simulation_time,
            payload=payload,
            pipeline_depth=4,
            streaming=True,
            monolithic=False,
            verbose=False
        )
        optimized_simpy_data.append({
            'Channels': n,
            'SimPy_BW': optimized_sim['aggregate_bandwidth']
        })
    
    baseline_simpy_df = pd.DataFrame(baseline_simpy_data)
    optimized_simpy_df = pd.DataFrame(optimized_simpy_data)
    
    if verbose:
        print("  Complete!\n")
    
    return {
        'baseline': ComparisonResult(
            name='baseline',
            analytical_df=baseline_analytical,
            simpy_df=baseline_simpy_df,
            config=baseline_config
        ),
        'optimized': ComparisonResult(
            name='optimized',
            analytical_df=optimized_analytical,
            simpy_df=optimized_simpy_df,
            config=optimized_config
        )
    }


def plot_comparison(results: Dict,
                   save_plots: bool = True,
                   show_plots: bool = True):
    """
    Generate comparison plots for analytical vs SimPy models.
    Saves all plots to 'assets/' directory.
    
    Args:
        results: Dictionary from run_channel_sweep()
        save_plots: Save plots to files
        show_plots: Display plots interactively
    """
    try:
        import matplotlib.pyplot as plt
        import seaborn as sns
        sns.set_style("whitegrid")
    except ImportError:
        print("Matplotlib not available. Cannot generate plots.")
        return
    
    # Create assets directory if it doesn't exist
    assets_dir = 'assets'
    if save_plots and not os.path.exists(assets_dir):
        os.makedirs(assets_dir)
        print(f"Created directory: {assets_dir}/")
    
    try:
        for name, result in results.items():
            analytical_df = result.analytical_df
            simpy_df = result.simpy_df
            
            fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 6))
            
            # Left plot: Bandwidth comparison
            ax1.plot(analytical_df['Channels'], analytical_df['Total_BW_GBps'],
                    'o-', linewidth=2.5, markersize=6, color='#2E86AB',
                    label='Analytical Model', alpha=0.8)
            ax1.plot(simpy_df['Channels'], simpy_df['SimPy_BW'],
                    's-', linewidth=2, markersize=7, color='#F18F01',
                    label='SimPy Simulation', alpha=0.8)
            
            # AXI peak line
            axi_peak = result.config.Bmax
            ax1.axhline(y=axi_peak, color='#C1121F', linestyle='--',
                       linewidth=2, alpha=0.6, label=f'AXI Peak: {axi_peak:.1f} GB/s')
            
            ax1.set_xlabel('Number of Channels', fontsize=13, fontweight='bold')
            ax1.set_ylabel('Read Bandwidth (GB/s)', fontsize=13, fontweight='bold')
            ax1.set_title(f'Read Path Aggregate Bandwidth: {name.title()}', fontsize=14, fontweight='bold')
            ax1.grid(True, alpha=0.3)
            ax1.legend(fontsize=11)
            ax1.set_xlim(left=0)
            ax1.set_ylim(bottom=0)
            
            # Right plot: Difference percentage
            # Interpolate SimPy to match analytical channels
            simpy_interp = np.interp(
                analytical_df['Channels'],
                simpy_df['Channels'],
                simpy_df['SimPy_BW']
            )
            diff_pct = ((simpy_interp - analytical_df['Total_BW_GBps']) / 
                       analytical_df['Total_BW_GBps']) * 100
            
            ax2.plot(analytical_df['Channels'], diff_pct, 'o-',
                    linewidth=2, markersize=5, color='#06A77D')
            ax2.axhline(y=0, color='black', linestyle='-', linewidth=1, alpha=0.5)
            ax2.axhline(y=5, color='red', linestyle='--', linewidth=1, alpha=0.5, label='±5% tolerance')
            ax2.axhline(y=-5, color='red', linestyle='--', linewidth=1, alpha=0.5)
            
            ax2.set_xlabel('Number of Channels', fontsize=13, fontweight='bold')
            ax2.set_ylabel('Difference (%)', fontsize=13, fontweight='bold')
            ax2.set_title(f'SimPy vs Analytical Difference: {name.title()}', fontsize=14, fontweight='bold')
            ax2.grid(True, alpha=0.3)
            ax2.legend(fontsize=11)
            ax2.set_xlim(left=0)
            
            plt.suptitle(f'Model Comparison: {name.title()}', fontsize=15, fontweight='bold', y=1.02)
            plt.tight_layout()
            
            if save_plots:
                filename = os.path.join(assets_dir, f'comparison_{name}.png')
                plt.savefig(filename, dpi=150, bbox_inches='tight')
                print(f"  ✓ Saved: {filename}")
            
            if show_plots:
                plt.show()
            else:
                plt.close()
        
        print("Plots complete!\n")
        
    except Exception as e:
        print(f"Error generating plots: {e}")


def create_comparison_table(results: Dict) -> pd.DataFrame:
    """
    Create summary table comparing models at key channel counts.
    
    Args:
        results: Dictionary from run_channel_sweep()
    
    Returns:
        DataFrame with comparison summary
    """
    rows = []
    
    for name, result in results.items():
        analytical_df = result.analytical_df
        simpy_df = result.simpy_df
        
        # Get data for key channel counts
        for n in simpy_df['Channels']:
            analytical_bw = analytical_df[analytical_df['Channels'] == n]['Total_BW_GBps'].iloc[0]
            simpy_bw = simpy_df[simpy_df['Channels'] == n]['SimPy_BW'].iloc[0]
            diff_pct = ((simpy_bw - analytical_bw) / analytical_bw) * 100
            
            rows.append({
                'Config': name.title(),
                'Channels': n,
                'Analytical_BW': analytical_bw,
                'SimPy_BW': simpy_bw,
                'Diff_%': diff_pct,
                'Within_5%': abs(diff_pct) <= 5
            })
    
    return pd.DataFrame(rows)


if __name__ == "__main__":
    print("\n" + "="*80)
    print("  MODEL COMPARISON: ANALYTICAL vs SIMPY")
    print("="*80 + "\n")
    
    # Run sweep
    print("Running channel sweep...")
    results = run_channel_sweep(
        max_channels=32,
        simulation_time=100000,
        payload=2048,
        verbose=True
    )
    
    # Create comparison table
    print("\nCreating comparison table...")
    comparison_df = create_comparison_table(results)
    print(comparison_df.to_string(index=False))
    print()
    
    # Save table
    try:
        os.makedirs('csv', exist_ok=True)
        comparison_df.to_csv('csv/model_comparison.csv', index=False)
        print("✓ Saved: csv/model_comparison.csv\n")
    except Exception as e:
        print(f"Could not save table: {e}\n")
    
    # Generate plots (saved to assets/)
    print("Generating comparison plots...")
    plot_comparison(results, save_plots=True, show_plots=False)
    
    print("="*80)
    print("Complete! Check the 'assets/' directory for generated plots.")
    print("="*80 + "\n")
