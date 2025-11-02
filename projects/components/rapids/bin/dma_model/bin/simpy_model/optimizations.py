# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: OptimizationStep
# Purpose: Incremental Optimization Framework for AXI4 Read Path
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Incremental Optimization Framework for AXI4 Read Path

This module allows step-by-step addition of optimizations to measure
their individual and combined impact on performance.

Usage:
    # Run all optimization steps
    results = run_optimization_sequence(num_channels=16)
    
    # Run specific optimization
    results = run_single_optimization(
        opt_name='pipelining',
        num_channels=16,
        pipeline_depth=4
    )
"""

import sys
import os
from typing import Dict, List, Tuple
import pandas as pd

# Add pyperf to path if needed
try:
    from simpy_model.current_design import (
        run_baseline_simulation, 
        run_optimized_simulation,
        ReadChannelConfig
    )
except ImportError:
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
    from simpy_model.current_design import (
        run_baseline_simulation,
        run_optimized_simulation,
        ReadChannelConfig
    )


class OptimizationStep:
    """Represents a single optimization step with configuration."""
    
    def __init__(self, name: str, description: str, 
                 pipeline_depth: int = 1,
                 streaming: bool = False,
                 monolithic: bool = False):
        self.name = name
        self.description = description
        self.pipeline_depth = pipeline_depth
        self.streaming = streaming
        self.monolithic = monolithic
    
    def __repr__(self):
        return f"OptimizationStep('{self.name}')"


# Define optimization sequence
OPTIMIZATION_SEQUENCE = [
    OptimizationStep(
        name="baseline",
        description="Current design: No pipelining, Store-and-Forward, Ping-Pong SRAM",
        pipeline_depth=1,
        streaming=False,
        monolithic=False
    ),
    OptimizationStep(
        name="pipeline_depth_2",
        description="Add pipelining with depth=2",
        pipeline_depth=2,
        streaming=False,
        monolithic=False
    ),
    OptimizationStep(
        name="pipeline_depth_4",
        description="Increase pipeline to depth=4",
        pipeline_depth=4,
        streaming=False,
        monolithic=False
    ),
    OptimizationStep(
        name="streaming_drain",
        description="Add streaming drain (no pipelining)",
        pipeline_depth=1,
        streaming=True,
        monolithic=False
    ),
    OptimizationStep(
        name="monolithic_sram",
        description="Use monolithic SRAM instead of ping-pong (no pipelining)",
        pipeline_depth=1,
        streaming=False,
        monolithic=True
    ),
    OptimizationStep(
        name="pipeline_plus_streaming",
        description="Combine pipelining (depth=4) + streaming drain",
        pipeline_depth=4,
        streaming=True,
        monolithic=False
    ),
    OptimizationStep(
        name="full_optimization",
        description="All optimizations: Pipeline (depth=4) + Streaming + Monolithic",
        pipeline_depth=4,
        streaming=True,
        monolithic=True
    ),
]


def run_single_optimization(opt_step: OptimizationStep,
                           num_channels: int = 16,
                           simulation_time: int = 100000,
                           payload: int = 2048,
                           verbose: bool = False) -> Dict:
    """
    Run simulation for a single optimization configuration.
    
    Args:
        opt_step: Optimization step configuration
        num_channels: Number of concurrent channels
        simulation_time: Simulation duration in cycles
        payload: Burst size in bytes
        verbose: Print detailed output
    
    Returns:
        Dictionary with results including config and statistics
    """
    if opt_step.name == "baseline":
        results = run_baseline_simulation(
            num_channels=num_channels,
            simulation_time=simulation_time,
            payload=payload,
            verbose=verbose
        )
    else:
        results = run_optimized_simulation(
            num_channels=num_channels,
            simulation_time=simulation_time,
            payload=payload,
            pipeline_depth=opt_step.pipeline_depth,
            streaming=opt_step.streaming,
            monolithic=opt_step.monolithic,
            verbose=verbose
        )
    
    # Add optimization info to results
    results['optimization'] = {
        'name': opt_step.name,
        'description': opt_step.description,
        'pipeline_depth': opt_step.pipeline_depth,
        'streaming': opt_step.streaming,
        'monolithic': opt_step.monolithic
    }
    
    return results


def run_optimization_sequence(num_channels: int = 16,
                             simulation_time: int = 100000,
                             payload: int = 2048,
                             steps: List[OptimizationStep] = None,
                             verbose: bool = False) -> Dict[str, Dict]:
    """
    Run full sequence of optimizations and collect results.
    
    Args:
        num_channels: Number of concurrent channels
        simulation_time: Simulation duration in cycles
        payload: Burst size in bytes
        steps: List of optimization steps (default: OPTIMIZATION_SEQUENCE)
        verbose: Print detailed output for each step
    
    Returns:
        Dictionary mapping optimization name to results
    """
    if steps is None:
        steps = OPTIMIZATION_SEQUENCE
    
    results = {}
    baseline_bw = None
    
    print(f"\n{'='*80}")
    print(f"  OPTIMIZATION SEQUENCE ANALYSIS")
    print(f"{'='*80}")
    print(f"\nSimulation Parameters:")
    print(f"  Channels:        {num_channels}")
    print(f"  Payload:         {payload} bytes")
    print(f"  Simulation Time: {simulation_time:,} cycles")
    print(f"  Steps:           {len(steps)}")
    print(f"\n{'='*80}\n")
    
    for i, step in enumerate(steps, 1):
        print(f"{i}. {step.name.upper().replace('_', ' ')}")
        print(f"   {step.description}")
        print("-" * 80)
        
        result = run_single_optimization(
            step,
            num_channels=num_channels,
            simulation_time=simulation_time,
            payload=payload,
            verbose=verbose
        )
        
        results[step.name] = result
        
        # Calculate improvement vs baseline
        if step.name == "baseline":
            baseline_bw = result['aggregate_bandwidth']
            print(f"   Bandwidth:     {baseline_bw:.3f} GB/s [BASELINE]")
        else:
            improvement = ((result['aggregate_bandwidth'] / baseline_bw) - 1) * 100
            print(f"   Bandwidth:     {result['aggregate_bandwidth']:.3f} GB/s "
                  f"(+{improvement:+.1f}% vs baseline)")
        
        print()
    
    # Print summary table
    print(f"\n{'='*80}")
    print(f"  SUMMARY")
    print(f"{'='*80}\n")
    
    print(f"{'Optimization':<30} {'BW (GB/s)':<12} {'Improvement':<15} {'Status':<10}")
    print("-" * 80)
    
    for step in steps:
        result = results[step.name]
        bw = result['aggregate_bandwidth']
        
        if step.name == "baseline":
            improvement_str = "baseline"
        else:
            improvement = ((bw / baseline_bw) - 1) * 100
            improvement_str = f"+{improvement:.1f}%"
        
        status = "✓" if bw >= 50 else ""
        print(f"{step.name:<30} {bw:>8.3f}     {improvement_str:<15} {status:<10}")
    
    print(f"\n{'='*80}")
    print(f"  KEY INSIGHTS")
    print(f"{'='*80}\n")
    
    # Analyze individual contributions
    if 'pipeline_depth_4' in results and 'streaming_drain' in results:
        pipe_gain = ((results['pipeline_depth_4']['aggregate_bandwidth'] / baseline_bw) - 1) * 100
        stream_gain = ((results['streaming_drain']['aggregate_bandwidth'] / baseline_bw) - 1) * 100
        
        print(f"Individual Optimizations:")
        print(f"  Pipelining (depth=4):    +{pipe_gain:.1f}%")
        print(f"  Streaming drain:         +{stream_gain:.1f}%")
        
        if 'pipeline_plus_streaming' in results:
            combined_gain = ((results['pipeline_plus_streaming']['aggregate_bandwidth'] / baseline_bw) - 1) * 100
            print(f"  Combined:                +{combined_gain:.1f}%")
            print(f"\n  Synergy: {combined_gain - pipe_gain - stream_gain:.1f}% "
                  f"(combined gain beyond sum of individual gains)")
    
    if 'full_optimization' in results:
        final_bw = results['full_optimization']['aggregate_bandwidth']
        final_gain = ((final_bw / baseline_bw) - 1) * 100
        print(f"\nFull Optimization:")
        print(f"  Baseline:     {baseline_bw:.2f} GB/s")
        print(f"  Optimized:    {final_bw:.2f} GB/s")
        print(f"  Total Gain:   +{final_gain:.1f}%")
        print(f"  Target Met:   {'✓ YES (50+ GB/s)' if final_bw >= 50 else '✗ NO'}")
    
    print(f"\n{'='*80}\n")
    
    return results


def create_comparison_dataframe(results: Dict[str, Dict]) -> pd.DataFrame:
    """
    Create a DataFrame summarizing all optimization results.
    
    Args:
        results: Dictionary from run_optimization_sequence()
    
    Returns:
        DataFrame with comparison data
    """
    rows = []
    
    baseline_bw = results['baseline']['aggregate_bandwidth'] if 'baseline' in results else None
    
    for name, result in results.items():
        opt = result['optimization']
        
        row = {
            'Optimization': name,
            'Description': opt['description'],
            'Pipeline_Depth': opt['pipeline_depth'],
            'Streaming': opt['streaming'],
            'Monolithic': opt['monolithic'],
            'Aggregate_BW_GBps': result['aggregate_bandwidth'],
            'Avg_Channel_BW_GBps': result['avg_channel_bandwidth'],
            'Total_Bursts': result['total_bursts'],
        }
        
        if baseline_bw:
            row['Improvement_%'] = ((result['aggregate_bandwidth'] / baseline_bw) - 1) * 100
        
        rows.append(row)
    
    df = pd.DataFrame(rows)
    return df


def analyze_incremental_gains(results: Dict[str, Dict]) -> Dict:
    """
    Analyze the incremental gain from each optimization step.
    
    Args:
        results: Dictionary from run_optimization_sequence()
    
    Returns:
        Dictionary with incremental analysis
    """
    analysis = {}
    
    # Define progression paths
    paths = {
        'pipelining_progression': [
            'baseline',
            'pipeline_depth_2',
            'pipeline_depth_4'
        ],
        'drain_modes': [
            'baseline',
            'streaming_drain'
        ],
        'sram_modes': [
            'baseline',
            'monolithic_sram'
        ],
        'combined_progression': [
            'baseline',
            'pipeline_depth_4',
            'pipeline_plus_streaming',
            'full_optimization'
        ]
    }
    
    for path_name, steps in paths.items():
        if all(step in results for step in steps):
            path_analysis = []
            prev_bw = None
            
            for step in steps:
                bw = results[step]['aggregate_bandwidth']
                
                if prev_bw is None:
                    incremental_gain = 0
                else:
                    incremental_gain = ((bw / prev_bw) - 1) * 100
                
                path_analysis.append({
                    'step': step,
                    'bandwidth': bw,
                    'incremental_gain_%': incremental_gain
                })
                
                prev_bw = bw
            
            analysis[path_name] = path_analysis
    
    return analysis


def print_incremental_analysis(analysis: Dict):
    """Print formatted incremental analysis."""
    print(f"\n{'='*80}")
    print(f"  INCREMENTAL GAIN ANALYSIS")
    print(f"{'='*80}\n")
    
    for path_name, path_data in analysis.items():
        print(f"{path_name.replace('_', ' ').title()}:")
        print("-" * 80)
        print(f"{'Step':<30} {'BW (GB/s)':<12} {'Incremental Gain':<20}")
        print("-" * 80)
        
        for i, data in enumerate(path_data):
            if i == 0:
                gain_str = "baseline"
            else:
                gain_str = f"+{data['incremental_gain_%']:.1f}%"
            
            print(f"{data['step']:<30} {data['bandwidth']:>8.3f}     {gain_str:<20}")
        
        print()
    
    print(f"{'='*80}\n")


if __name__ == "__main__":
    # Run full optimization sequence
    results = run_optimization_sequence(
        num_channels=16,
        simulation_time=100000,
        payload=2048,
        verbose=False  # Set to True for detailed per-step output
    )
    
    # Create comparison DataFrame
    df = create_comparison_dataframe(results)
    print("\nComparison DataFrame:")
    print("="*80)
    print(df.to_string(index=False))
    print()
    
    # Analyze incremental gains
    analysis = analyze_incremental_gains(results)
    print_incremental_analysis(analysis)
    
    # Optional: Save results
    try:
        os.makedirs('csv', exist_ok=True)
        df.to_csv('csv/optimization_results.csv', index=False)
        print("Results saved to: csv/optimization_results.csv\n")
    except Exception as e:
        print(f"Could not save results: {e}\n")
