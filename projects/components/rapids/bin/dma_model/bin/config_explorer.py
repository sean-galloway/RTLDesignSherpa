#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: config_explorer
# Purpose: Configuration Explorer
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Configuration Explorer

Interactive tool to explore different AXI4 configurations and their impact
on performance.

Usage:
    # Interactive mode
    python config_explorer.py
    
    # Command-line mode
    python config_explorer.py --channels 16 --payload 2048 --pipeline 4 --streaming --compare
"""

import sys
import os
import argparse

# Add project root to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from analytical import get_baseline_performance, get_optimized_performance
from simpy_model import run_baseline_simulation, run_optimized_simulation


def explore_configuration(channels=16, payload=2048, pipeline_depth=1,
                         streaming=False, monolithic=False,
                         use_simpy=False, simulation_time=50000):
    """
    Explore a specific configuration.
    
    Args:
        channels: Number of channels
        payload: Burst size in bytes
        pipeline_depth: Pipeline depth
        streaming: Enable streaming drain
        monolithic: Use monolithic SRAM
        use_simpy: Use SimPy instead of analytical
        simulation_time: SimPy simulation time
    
    Returns:
        Performance results
    """
    print("\n" + "="*80)
    print("  CONFIGURATION EXPLORER - READ PATH")
    print("="*80)
    
    print(f"\nConfiguration:")
    print(f"  Channels:       {channels}")
    print(f"  Payload:        {payload} bytes")
    print(f"  Pipeline Depth: {pipeline_depth}")
    print(f"  Streaming:      {'Yes' if streaming else 'No'}")
    print(f"  SRAM Mode:      {'Monolithic' if monolithic else 'Ping-Pong'}")
    print(f"  Model:          {'SimPy' if use_simpy else 'Analytical'}")
    
    if use_simpy:
        print(f"  Sim Time:       {simulation_time:,} cycles")
    
    print()
    
    # Determine if this is baseline or optimized
    is_baseline = (pipeline_depth == 1 and not streaming and not monolithic)
    
    # Run model
    if use_simpy:
        print("Running SimPy simulation...")
        if is_baseline:
            results = run_baseline_simulation(
                num_channels=channels,
                simulation_time=simulation_time,
                payload=payload,
                verbose=False
            )
        else:
            results = run_optimized_simulation(
                num_channels=channels,
                simulation_time=simulation_time,
                payload=payload,
                pipeline_depth=pipeline_depth,
                streaming=streaming,
                monolithic=monolithic,
                verbose=False
            )
        
        # Extract key metrics
        aggregate_bw = results['aggregate_bandwidth']
        per_channel_bw = results['avg_channel_bandwidth']
        total_bursts = results['total_bursts']
        
        print("\nResults (Read Path):")
        print(f"  Total Bursts:       {total_bursts:,}")
        print(f"  Aggregate Read BW:  {aggregate_bw:.3f} GB/s")
        print(f"  Per-Channel Read:   {per_channel_bw:.3f} GB/s")
        
        # Timing breakdown
        timing = results['timing_breakdown']
        print(f"\nTiming Breakdown (avg per burst):")
        print(f"  Latency:            {timing['avg_latency_cycles']:.1f} cycles")
        print(f"  Data Return:        {timing['avg_data_return_cycles']:.1f} cycles")
        print(f"  Drain:              {timing['avg_drain_cycles']:.1f} cycles")
        total_cycles = sum(timing.values())
        print(f"  Total:              {total_cycles:.1f} cycles")
        
    else:
        print("Running analytical model...")
        if is_baseline:
            result_data = get_baseline_performance(verbose=False)
        else:
            result_data = get_optimized_performance(
                pipeline_depth=pipeline_depth,
                streaming=streaming,
                monolithic=monolithic,
                payload=payload,
                verbose=False
            )
        
        perf = result_data['performance']
        config = result_data['config']
        result = perf.calculate_channel_bandwidth(channels)
        
        aggregate_bw = result['total_bw']
        per_channel_bw = result['B_channel']
        
        print("\nResults (Read Path):")
        print(f"  Aggregate Read BW:  {aggregate_bw:.3f} GB/s")
        print(f"  Per-Channel Read:   {per_channel_bw:.3f} GB/s")
        print(f"  Efficiency:         {result['efficiency']:.1f}% of AXI peak")
        print(f"  Limited By:         {result['limited_by']}")
        print(f"  Cycles per Burst:   {result['cycles_per_burst']:.1f}")
        
        # SRAM info
        print(f"\nSRAM Info:")
        print(f"  Mode:               {config.sram_mode.title()}")
        print(f"  Max Pipeline Depth: {config.max_sram_pipeline_depth}")
        print(f"  Effective Depth:    {result['effective_pipeline_depth']}")
        if result['sram_limited']:
            print(f"  ⚠️  SRAM limits pipeline depth!")
    
    # Performance assessment
    print(f"\nPerformance Assessment:")
    target = 50.0
    meets_target = aggregate_bw >= target
    print(f"  Target (50+ GB/s):  {'✓ MET' if meets_target else '✗ NOT MET'}")
    
    per_channel_cap = 4.0
    utilization = (per_channel_bw / per_channel_cap) * 100
    print(f"  Per-Ch Utilization: {utilization:.1f}% of {per_channel_cap} GB/s cap")
    
    print("\n" + "="*80 + "\n")
    
    return {
        'config': {
            'channels': channels,
            'payload': payload,
            'pipeline_depth': pipeline_depth,
            'streaming': streaming,
            'monolithic': monolithic
        },
        'results': {
            'aggregate_bw': aggregate_bw,
            'per_channel_bw': per_channel_bw,
            'meets_target': meets_target
        }
    }


def compare_configurations(configs, use_simpy=False, simulation_time=50000):
    """
    Compare multiple configurations side-by-side.
    
    Args:
        configs: List of configuration dictionaries
        use_simpy: Use SimPy instead of analytical
        simulation_time: SimPy simulation time
    
    Returns:
        Comparison results
    """
    print("\n" + "="*80)
    print("  CONFIGURATION COMPARISON")
    print("="*80)
    print(f"\nComparing {len(configs)} configurations...")
    print(f"Model: {'SimPy' if use_simpy else 'Analytical'}")
    print()
    
    results = []
    
    for i, config in enumerate(configs, 1):
        print(f"[{i}/{len(configs)}] Running: ", end='')
        
        # Print config summary
        parts = []
        if config.get('pipeline_depth', 1) > 1:
            parts.append(f"pipeline={config['pipeline_depth']}")
        if config.get('streaming', False):
            parts.append("streaming")
        if config.get('monolithic', False):
            parts.append("monolithic")
        
        if not parts:
            config_str = "baseline"
        else:
            config_str = ", ".join(parts)
        
        print(config_str)
        
        result = explore_configuration(
            channels=config.get('channels', 16),
            payload=config.get('payload', 2048),
            pipeline_depth=config.get('pipeline_depth', 1),
            streaming=config.get('streaming', False),
            monolithic=config.get('monolithic', False),
            use_simpy=use_simpy,
            simulation_time=simulation_time
        )
        
        results.append(result)
    
    # Print comparison table
    print("\n" + "="*80)
    print("  COMPARISON SUMMARY - READ PATH")
    print("="*80 + "\n")
    
    print(f"{'Config':<25} {'Channels':<10} {'Pipeline':<10} {'Stream':<8} {'Read BW':<15} {'Target':<10}")
    print("-" * 95)
    
    for i, (config, result) in enumerate(zip(configs, results), 1):
        name = config.get('name', f'Config {i}')
        channels = config.get('channels', 16)
        pipeline = config.get('pipeline_depth', 1)
        streaming = 'Yes' if config.get('streaming', False) else 'No'
        bw = result['results']['aggregate_bw']
        target_met = '✓' if result['results']['meets_target'] else '✗'
        
        print(f"{name:<25} {channels:<10} {pipeline:<10} {streaming:<8} {bw:>8.2f} GB/s   {target_met:<10}")
    
    # Find best configuration
    best_idx = max(range(len(results)), key=lambda i: results[i]['results']['aggregate_bw'])
    best_bw = results[best_idx]['results']['aggregate_bw']
    
    print("-" * 95)
    print(f"{'Best Configuration:':<25} {configs[best_idx].get('name', f'Config {best_idx+1}')} "
          f"with {best_bw:.2f} GB/s")
    
    print("\n" + "="*80 + "\n")
    
    return results


def interactive_mode():
    """Interactive configuration explorer."""
    print("\n" + "="*80)
    print("  INTERACTIVE CONFIGURATION EXPLORER - READ PATH")
    print("="*80)
    
    print("\nThis tool helps you explore different AXI4 read configurations.")
    print("You can modify parameters and see their impact on read performance.")
    
    # Get configuration from user
    print("\nEnter configuration parameters (press Enter for defaults):")
    
    try:
        channels = input("  Number of channels [16]: ").strip()
        channels = int(channels) if channels else 16
        
        payload = input("  Payload size in bytes [2048]: ").strip()
        payload = int(payload) if payload else 2048
        
        pipeline = input("  Pipeline depth [1]: ").strip()
        pipeline = int(pipeline) if pipeline else 1
        
        streaming = input("  Enable streaming drain? (y/n) [n]: ").strip().lower()
        streaming = streaming == 'y'
        
        monolithic = input("  Use monolithic SRAM? (y/n) [n]: ").strip().lower()
        monolithic = monolithic == 'y'
        
        model = input("  Use SimPy simulation? (y/n) [n]: ").strip().lower()
        use_simpy = model == 'y'
        
        if use_simpy:
            sim_time = input("  Simulation time in cycles [50000]: ").strip()
            sim_time = int(sim_time) if sim_time else 50000
        else:
            sim_time = 50000
        
        # Run exploration
        result = explore_configuration(
            channels=channels,
            payload=payload,
            pipeline_depth=pipeline,
            streaming=streaming,
            monolithic=monolithic,
            use_simpy=use_simpy,
            simulation_time=sim_time
        )
        
        # Ask if user wants to compare
        compare = input("\nCompare with other configurations? (y/n) [n]: ").strip().lower()
        
        if compare == 'y':
            # Define common configurations to compare
            configs = [
                {
                    'name': 'Baseline',
                    'channels': channels,
                    'payload': payload,
                    'pipeline_depth': 1,
                    'streaming': False,
                    'monolithic': False
                },
                {
                    'name': 'Your Config',
                    'channels': channels,
                    'payload': payload,
                    'pipeline_depth': pipeline,
                    'streaming': streaming,
                    'monolithic': monolithic
                },
                {
                    'name': 'Optimized (P=4+Stream)',
                    'channels': channels,
                    'payload': payload,
                    'pipeline_depth': 4,
                    'streaming': True,
                    'monolithic': False
                }
            ]
            
            compare_configurations(configs, use_simpy=use_simpy, simulation_time=sim_time)
        
    except KeyboardInterrupt:
        print("\n\nExiting...")
        return
    except Exception as e:
        print(f"\nError: {e}")
        return


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='Explore AXI4 performance configurations',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument('--channels', type=int, help='Number of channels')
    parser.add_argument('--payload', type=int, help='Payload size in bytes')
    parser.add_argument('--pipeline', type=int, help='Pipeline depth')
    parser.add_argument('--streaming', action='store_true', help='Enable streaming drain')
    parser.add_argument('--monolithic', action='store_true', help='Use monolithic SRAM')
    parser.add_argument('--simpy', action='store_true', help='Use SimPy simulation')
    parser.add_argument('--sim-time', type=int, default=50000, help='Simulation time')
    parser.add_argument('--compare', action='store_true', help='Compare with standard configs')
    
    args = parser.parse_args()
    
    # If no arguments, run interactive mode
    if len(sys.argv) == 1:
        interactive_mode()
        return 0
    
    # Otherwise, run with command-line args
    try:
        result = explore_configuration(
            channels=args.channels if args.channels else 16,
            payload=args.payload if args.payload else 2048,
            pipeline_depth=args.pipeline if args.pipeline else 1,
            streaming=args.streaming,
            monolithic=args.monolithic,
            use_simpy=args.simpy,
            simulation_time=args.sim_time
        )
        
        if args.compare:
            channels = args.channels if args.channels else 16
            payload = args.payload if args.payload else 2048
            
            configs = [
                {
                    'name': 'Baseline',
                    'channels': channels,
                    'payload': payload,
                    'pipeline_depth': 1,
                    'streaming': False,
                    'monolithic': False
                },
                {
                    'name': 'Your Config',
                    'channels': channels,
                    'payload': payload,
                    'pipeline_depth': args.pipeline if args.pipeline else 1,
                    'streaming': args.streaming,
                    'monolithic': args.monolithic
                },
                {
                    'name': 'Optimized',
                    'channels': channels,
                    'payload': payload,
                    'pipeline_depth': 4,
                    'streaming': True,
                    'monolithic': False
                }
            ]
            
            compare_configurations(configs, use_simpy=args.simpy, simulation_time=args.sim_time)
        
        return 0
        
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
