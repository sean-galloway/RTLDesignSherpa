# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: sram_analysis
# Purpose: SRAM Sizing Analysis for AXI4 Read Path
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
SRAM Sizing Analysis for AXI4 Read Path

This module analyzes optimal SRAM configurations including:
- Ping-pong vs Monolithic SRAM comparison  
- SRAM size requirements for different pipeline depths
- Payload size impact on SRAM efficiency
- Cost-benefit analysis of SRAM sizing

Usage:
    # Run complete analysis
    python analytical/sram_analysis.py
    
    # Or import and use programmatically
    from analytical.sram_analysis import (
        compare_sram_modes,
        find_optimal_sram_size,
        analyze_payload_vs_sram,
        run_sram_analysis
    )
    
    # Compare modes
    results = compare_sram_modes(payload=2048, pipeline_depth=4)
    
    # Find optimal size  
    optimal = find_optimal_sram_size(payload=2048, target_bandwidth=50.0)
    
    # Run full analysis
    all_results = run_sram_analysis(num_channels=16, streaming=True)
"""

import sys
import os
import pandas as pd
import numpy as np
from typing import Dict, List, Tuple, Optional

# Add paths
try:
    from pyperf import AXIConfig, AXI4Performance
except ImportError:
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
    from pyperf import AXIConfig, AXI4Performance


def calculate_sram_requirements(payload: int, 
                                pipeline_depth: int,
                                sram_mode: str = "pingpong") -> Dict:
    """
    Calculate SRAM requirements for given configuration.
    
    Args:
        payload: Burst size in bytes
        pipeline_depth: Desired pipeline depth
        sram_mode: "pingpong" or "monolithic"
    
    Returns:
        Dictionary with SRAM sizing information
    """
    if sram_mode == "pingpong":
        # Ping-pong: Always 2 slots, each must hold full payload
        num_slots = 2
        slot_size = payload  # Each slot must hold one burst
        total_sram = num_slots * slot_size
        max_pipeline = 2  # Limited by number of slots
        effective_pipeline = min(pipeline_depth, max_pipeline)
        sram_limited = pipeline_depth > max_pipeline
        utilization = (effective_pipeline * payload) / total_sram * 100
        
    else:  # monolithic
        # Monolithic: Single buffer, allocate exactly what's needed
        total_sram = pipeline_depth * payload
        num_slots = 1
        slot_size = total_sram
        max_pipeline = pipeline_depth  # Can support requested depth
        effective_pipeline = pipeline_depth
        sram_limited = False
        utilization = 100.0  # Always 100% by design
    
    return {
        'payload': payload,
        'pipeline_depth_requested': pipeline_depth,
        'sram_mode': sram_mode,
        'num_slots': num_slots,
        'slot_size_bytes': slot_size,
        'total_sram_bytes': total_sram,
        'total_sram_kb': total_sram / 1024,
        'max_pipeline_depth': max_pipeline,
        'effective_pipeline_depth': effective_pipeline,
        'sram_limited': sram_limited,
        'utilization_%': utilization,
        'waste_bytes': total_sram - (effective_pipeline * payload),
    }


def compare_sram_modes(payload: int,
                    pipeline_depth: int,
                    num_channels: int = 16,
                    verbose: bool = True) -> Dict:
    """
    Compare ping-pong vs monolithic SRAM for a configuration.
    
    Args:
        payload: Burst size in bytes
        pipeline_depth: Desired pipeline depth
        num_channels: Number of channels
        verbose: Print comparison
    
    Returns:
        Dictionary with comparison results
    """
    # Calculate SRAM requirements
    pingpong_req = calculate_sram_requirements(payload, pipeline_depth, "pingpong")
    monolithic_req = calculate_sram_requirements(payload, pipeline_depth, "monolithic")
    
    # Calculate performance for each mode
    config_pp = AXIConfig(
        payload=payload,
        pipeline_depth=pipeline_depth,
        pipelining_enabled=(pipeline_depth > 1),
        streaming_drain=False,
        sram_mode="pingpong"
    )
    
    config_mono = AXIConfig(
        payload=payload,
        pipeline_depth=pipeline_depth,
        pipelining_enabled=(pipeline_depth > 1),
        streaming_drain=False,
        sram_mode="monolithic"
    )
    
    perf_pp = AXI4Performance(config_pp)
    perf_mono = AXI4Performance(config_mono)
    
    result_pp = perf_pp.calculate_channel_bandwidth(num_channels)
    result_mono = perf_mono.calculate_channel_bandwidth(num_channels)
    
    # Per-channel SRAM (all channels need same amount)
    total_sram_pp = pingpong_req['total_sram_bytes'] * num_channels
    total_sram_mono = monolithic_req['total_sram_bytes'] * num_channels
    
    if verbose:
        print(f"\n{'='*80}")
        print(f"  SRAM MODE COMPARISON")
        print(f"{'='*80}")
        print(f"\nConfiguration:")
        print(f"  Payload:          {payload} bytes")
        print(f"  Pipeline Depth:   {pipeline_depth}")
        print(f"  Channels:         {num_channels}")
        print()
        
        print(f"{'Metric':<35} {'Ping-Pong':<20} {'Monolithic':<20}")
        print("-" * 80)
        print(f"{'SRAM per channel:':<35} {pingpong_req['total_sram_bytes']:>8} bytes       "
            f"{monolithic_req['total_sram_bytes']:>8} bytes")
        print(f"{'SRAM per channel:':<35} {pingpong_req['total_sram_kb']:>8.2f} KB          "
            f"{monolithic_req['total_sram_kb']:>8.2f} KB")
        print(f"{'Total SRAM ({num_channels} channels):':<35} {total_sram_pp/1024:>8.2f} KB          "
            f"{total_sram_mono/1024:>8.2f} KB")
        print(f"{'Max pipeline depth:':<35} {pingpong_req['max_pipeline_depth']:>8}             "
            f"{monolithic_req['max_pipeline_depth']:>8}")
        print(f"{'Effective pipeline:':<35} {result_pp['effective_pipeline_depth']:>8}             "
            f"{result_mono['effective_pipeline_depth']:>8}")
        print(f"{'SRAM utilization:':<35} {pingpong_req['utilization_%']:>8.1f}%           "
            f"{monolithic_req['utilization_%']:>8.1f}%")
        print(f"{'SRAM limited:':<35} {str(pingpong_req['sram_limited']):<20} "
            f"{str(monolithic_req['sram_limited']):<20}")
        print()
        print(f"{'Performance:':<35}")
        print(f"{'  Single channel BW:':<35} {result_pp['B_channel']:>8.3f} GB/s       "
            f"{result_mono['B_channel']:>8.3f} GB/s")
        print(f"{'  Total BW ({num_channels} ch):':<35} {result_pp['total_bw']:>8.2f} GB/s       "
            f"{result_mono['total_bw']:>8.2f} GB/s")
        
        # Determine winner
        if result_mono['total_bw'] > result_pp['total_bw']:
            winner = "Monolithic"
            bw_advantage = ((result_mono['total_bw'] / result_pp['total_bw']) - 1) * 100
            sram_cost = ((total_sram_mono - total_sram_pp) / total_sram_pp) * 100
        elif result_pp['total_bw'] > result_mono['total_bw']:
            winner = "Ping-Pong"
            bw_advantage = ((result_pp['total_bw'] / result_mono['total_bw']) - 1) * 100
            sram_cost = ((total_sram_pp - total_sram_mono) / total_sram_mono) * 100
        else:
            winner = "Tie"
            bw_advantage = 0
            sram_cost = ((total_sram_pp - total_sram_mono) / max(total_sram_mono, total_sram_pp)) * 100
        
        print()
        print(f"{'='*80}")
        print(f"  RECOMMENDATION")
        print(f"{'='*80}")
        if winner == "Tie":
            print(f"\nBoth modes achieve same performance ({result_pp['total_bw']:.2f} GB/s)")
            if total_sram_pp < total_sram_mono:
                print(f"âœ… Choose Ping-Pong: Uses {abs(sram_cost):.1f}% less SRAM")
            elif total_sram_mono < total_sram_pp:
                print(f"âœ… Choose Monolithic: Uses {abs(sram_cost):.1f}% less SRAM")
            else:
                print(f"âœ… Either mode works: Same SRAM usage")
        else:
            print(f"\nâœ… Choose {winner}:")
            print(f"  Performance advantage: +{bw_advantage:.1f}%")
            print(f"  SRAM cost: {'+' if sram_cost > 0 else ''}{sram_cost:.1f}%")
        print(f"\n{'='*80}\n")
    
    return {
        'pingpong': {
            'requirements': pingpong_req,
            'performance': result_pp,
            'total_sram_bytes': total_sram_pp,
            'total_sram_kb': total_sram_pp / 1024
        },
        'monolithic': {
            'requirements': monolithic_req,
            'performance': result_mono,
            'total_sram_bytes': total_sram_mono,
            'total_sram_kb': total_sram_mono / 1024
        },
        'recommendation': {
            'winner': winner if winner != "Tie" else "Both equal",
            'bandwidth_advantage_%': bw_advantage if winner != "Tie" else 0,
            'sram_cost_difference_%': sram_cost
        }
    }


def analyze_payload_vs_sram(payloads: List[int] = None,
                        pipeline_depths: List[int] = None,
                        num_channels: int = 16,
                        verbose: bool = True) -> pd.DataFrame:
    """
    Analyze SRAM requirements across different payloads and pipeline depths.
    
    Args:
        payloads: List of payload sizes to test (default: [256, 512, 1024, 2048])
        pipeline_depths: List of pipeline depths (default: [1, 2, 4, 8])
        num_channels: Number of channels
        verbose: Print summary
    
    Returns:
        DataFrame with comprehensive SRAM analysis
    """
    if payloads is None:
        payloads = [256, 512, 1024, 2048]
    
    if pipeline_depths is None:
        pipeline_depths = [1, 2, 4, 8]
    
    results = []
    
    for payload in payloads:
        for depth in pipeline_depths:
            # Ping-pong
            pp_req = calculate_sram_requirements(payload, depth, "pingpong")
            config_pp = AXIConfig(
                payload=payload,
                pipeline_depth=depth,
                pipelining_enabled=(depth > 1),
                sram_mode="pingpong"
            )
            perf_pp = AXI4Performance(config_pp)
            result_pp = perf_pp.calculate_channel_bandwidth(num_channels)
            
            # Monolithic
            mono_req = calculate_sram_requirements(payload, depth, "monolithic")
            config_mono = AXIConfig(
                payload=payload,
                pipeline_depth=depth,
                pipelining_enabled=(depth > 1),
                sram_mode="monolithic"
            )
            perf_mono = AXI4Performance(config_mono)
            result_mono = perf_mono.calculate_channel_bandwidth(num_channels)
            
            # Determine better option
            if result_mono['total_bw'] > result_pp['total_bw']:
                better = "Monolithic"
                bw_gain = ((result_mono['total_bw'] / result_pp['total_bw']) - 1) * 100
            elif result_pp['total_bw'] > result_mono['total_bw']:
                better = "Ping-Pong"
                bw_gain = ((result_pp['total_bw'] / result_mono['total_bw']) - 1) * 100
            else:
                better = "Equal"
                bw_gain = 0
            
            results.append({
                'Payload_Bytes': payload,
                'Pipeline_Depth': depth,
                'PP_SRAM_KB_per_ch': pp_req['total_sram_kb'],
                'PP_Total_SRAM_KB': pp_req['total_sram_kb'] * num_channels,
                'PP_Effective_Depth': result_pp['effective_pipeline_depth'],
                'PP_BW_GBps': result_pp['total_bw'],
                'Mono_SRAM_KB_per_ch': mono_req['total_sram_kb'],
                'Mono_Total_SRAM_KB': mono_req['total_sram_kb'] * num_channels,
                'Mono_Effective_Depth': result_mono['effective_pipeline_depth'],
                'Mono_BW_GBps': result_mono['total_bw'],
                'Better_Mode': better,
                'BW_Gain_%': bw_gain,
            })
    
    df = pd.DataFrame(results)
    
    if verbose:
        print(f"\n{'='*80}")
        print(f"  SRAM SIZING ANALYSIS: Payload vs Pipeline Depth")
        print(f"{'='*80}")
        print(f"\nAnalysis: {num_channels} channels\n")
        print(df.to_string(index=False))
        
        print(f"\n{'='*80}")
        print(f"  KEY INSIGHTS")
        print(f"{'='*80}\n")
        
        # Group by payload and find crossover points
        for payload in payloads:
            subset = df[df['Payload_Bytes'] == payload]
            
            # Find where monolithic becomes better
            mono_better = subset[subset['Better_Mode'] == 'Monolithic']
            if not mono_better.empty:
                min_depth = mono_better['Pipeline_Depth'].min()
                print(f"Payload {payload}B:")
                print(f"  - Monolithic better at depth â‰¥ {min_depth}")
                print(f"  - Max ping-pong depth: 2 (always)")
                print(f"  - Max monolithic depth @ 4KB: {4096 // payload}")
            else:
                print(f"Payload {payload}B:")
                print(f"  - Ping-pong sufficient for all tested depths")
                print(f"  - Both modes achieve same performance")
            print()
        
        print(f"{'='*80}\n")
    
    return df


def find_optimal_sram_size(payload: int,
                        target_bandwidth: float,
                        num_channels: int = 16,
                        streaming: bool = True,
                        verbose: bool = True) -> Dict:
    """
    Find minimum SRAM size needed to achieve target bandwidth.
    
    Args:
        payload: Burst size in bytes
        target_bandwidth: Target aggregate bandwidth in GB/s
        num_channels: Number of channels
        streaming: Enable streaming drain
        verbose: Print analysis
    
    Returns:
        Dictionary with optimal configuration
    """
    if verbose:
        print(f"\n{'='*80}")
        print(f"  OPTIMAL SRAM SIZING")
        print(f"{'='*80}")
        print(f"\nTarget: {target_bandwidth} GB/s with {num_channels} channels")
        print(f"Payload: {payload} bytes")
        print(f"Streaming: {'Enabled' if streaming else 'Disabled'}\n")
    
    # Test increasing pipeline depths
    max_test_depth = 16
    results = []
    
    for depth in range(1, max_test_depth + 1):
        # Test both modes
        for mode in ['pingpong', 'monolithic']:
            config = AXIConfig(
                payload=payload,
                pipeline_depth=depth,
                pipelining_enabled=(depth > 1),
                streaming_drain=streaming,
                sram_mode=mode
            )
            
            perf = AXI4Performance(config)
            result = perf.calculate_channel_bandwidth(num_channels)
            
            sram_req = calculate_sram_requirements(payload, depth, mode)
            total_sram = sram_req['total_sram_bytes'] * num_channels
            
            results.append({
                'pipeline_depth': depth,
                'sram_mode': mode,
                'effective_depth': result['effective_pipeline_depth'],
                'sram_per_ch_kb': sram_req['total_sram_kb'],
                'total_sram_kb': total_sram / 1024,
                'bandwidth': result['total_bw'],
                'meets_target': result['total_bw'] >= target_bandwidth
            })
    
    df = pd.DataFrame(results)
    
    # Find minimum SRAM for each mode that meets target
    optimal = {}
    
    for mode in ['pingpong', 'monolithic']:
        mode_df = df[df['sram_mode'] == mode]
        meets_target = mode_df[mode_df['meets_target']]
        
        if not meets_target.empty:
            best = meets_target.iloc[0]  # First one that meets target (minimum SRAM)
            optimal[mode] = {
                'pipeline_depth': int(best['pipeline_depth']),
                'effective_depth': int(best['effective_depth']),
                'sram_per_ch_kb': best['sram_per_ch_kb'],
                'total_sram_kb': best['total_sram_kb'],
                'bandwidth': best['bandwidth'],
                'achievable': True
            }
        else:
            # Can't meet target with this mode
            best = mode_df.iloc[-1]  # Best effort
            optimal[mode] = {
                'pipeline_depth': int(best['pipeline_depth']),
                'effective_depth': int(best['effective_depth']),
                'sram_per_ch_kb': best['sram_per_ch_kb'],
                'total_sram_kb': best['total_sram_kb'],
                'bandwidth': best['bandwidth'],
                'achievable': False
            }
    
    if verbose:
        print(f"{'Mode':<15} {'Pipeline':<10} {'SRAM/ch':<12} {'Total SRAM':<15} {'BW':<12} {'Status':<15}")
        print("-" * 90)
        
        for mode in ['pingpong', 'monolithic']:
            opt = optimal[mode]
            status = " Achievable" if opt['achievable'] else "âœ— Not achievable"
            print(f"{mode:<15} {opt['pipeline_depth']:<10} {opt['sram_per_ch_kb']:>8.2f} KB  "
                f"{opt['total_sram_kb']:>10.2f} KB   {opt['bandwidth']:>8.2f} GB/s  {status:<15}")
        
        print(f"\n{'='*80}")
        print(f"  RECOMMENDATION")
        print(f"{'='*80}\n")
        
        # Determine best option
        pp_achievable = optimal['pingpong']['achievable']
        mono_achievable = optimal['monolithic']['achievable']
        
        if pp_achievable and mono_achievable:
            # Both work, choose one with less SRAM
            if optimal['pingpong']['total_sram_kb'] <= optimal['monolithic']['total_sram_kb']:
                best_mode = 'pingpong'
            else:
                best_mode = 'monolithic'
            
            best = optimal[best_mode]
            other_mode = 'monolithic' if best_mode == 'pingpong' else 'pingpong'
            other = optimal[other_mode]
            
            sram_savings = ((other['total_sram_kb'] - best['total_sram_kb']) / other['total_sram_kb']) * 100
            
            print(f"âœ… Use {best_mode.upper()} SRAM:")
            print(f"  Pipeline depth: {best['pipeline_depth']}")
            print(f"  SRAM per channel: {best['sram_per_ch_kb']:.2f} KB")
            print(f"  Total SRAM: {best['total_sram_kb']:.2f} KB")
            print(f"  Bandwidth: {best['bandwidth']:.2f} GB/s")
            print(f"  SRAM savings vs {other_mode}: {sram_savings:.1f}%")
            
        elif pp_achievable:
            best = optimal['pingpong']
            print(f"âœ… Use PING-PONG SRAM:")
            print(f"  Pipeline depth: {best['pipeline_depth']}")
            print(f"  SRAM per channel: {best['sram_per_ch_kb']:.2f} KB")
            print(f"  Total SRAM: {best['total_sram_kb']:.2f} KB")
            print(f"  Bandwidth: {best['bandwidth']:.2f} GB/s")
            
        elif mono_achievable:
            best = optimal['monolithic']
            print(f"âœ… Use MONOLITHIC SRAM:")
            print(f"  Pipeline depth: {best['pipeline_depth']}")
            print(f"  SRAM per channel: {best['sram_per_ch_kb']:.2f} KB")
            print(f"  Total SRAM: {best['total_sram_kb']:.2f} KB")
            print(f"  Bandwidth: {best['bandwidth']:.2f} GB/s")
            
        else:
            print(f"âš ï¸  Target not achievable with {payload}B payload")
            print(f"\nBest effort:")
            best_bw = max(optimal['pingpong']['bandwidth'], optimal['monolithic']['bandwidth'])
            if optimal['pingpong']['bandwidth'] >= optimal['monolithic']['bandwidth']:
                best_mode = 'pingpong'
            else:
                best_mode = 'monolithic'
            
            best = optimal[best_mode]
            shortfall = target_bandwidth - best['bandwidth']
            print(f"  Mode: {best_mode}")
            print(f"  Max BW: {best['bandwidth']:.2f} GB/s")
            print(f"  Shortfall: {shortfall:.2f} GB/s ({shortfall/target_bandwidth*100:.1f}%)")
            print(f"\nConsider:")
            print(f"  - Smaller payload size")
            print(f"  - More channels")
            print(f"  - Streaming drain (if not enabled)")
        
        print(f"\n{'='*80}\n")
    
    return optimal


def generate_sram_recommendation_table(num_channels: int = 16,
                                    streaming: bool = True,
                                    verbose: bool = True) -> pd.DataFrame:
    """
    Generate comprehensive SRAM sizing recommendations.
    
    Args:
        num_channels: Number of channels
        streaming: Enable streaming drain
        verbose: Print table
    
    Returns:
        DataFrame with recommendations
    """
    configurations = [
        {'payload': 256, 'target_bw': 50},
        {'payload': 512, 'target_bw': 50},
        {'payload': 1024, 'target_bw': 50},
        {'payload': 2048, 'target_bw': 50},
    ]
    
    results = []
    
    for config in configurations:
        payload = config['payload']
        target = config['target_bw']
        
        # Test both modes
        for mode in ['pingpong', 'monolithic']:
            # Find minimum depth that meets target
            for depth in range(1, 17):
                cfg = AXIConfig(
                    payload=payload,
                    pipeline_depth=depth,
                    pipelining_enabled=(depth > 1),
                    streaming_drain=streaming,
                    sram_mode=mode
                )
                
                perf = AXI4Performance(cfg)
                result = perf.calculate_channel_bandwidth(num_channels)
                
                if result['total_bw'] >= target:
                    sram_req = calculate_sram_requirements(payload, depth, mode)
                    
                    results.append({
                        'Payload_Bytes': payload,
                        'SRAM_Mode': mode,
                        'Min_Pipeline_Depth': depth,
                        'Effective_Depth': result['effective_pipeline_depth'],
                        'SRAM_per_ch_KB': sram_req['total_sram_kb'],
                        'Total_SRAM_KB': sram_req['total_sram_kb'] * num_channels,
                        'Bandwidth_GBps': result['total_bw'],
                        'Target_Met': 'âœ"'
                    })
                    break
            else:
                # Couldn't meet target
                results.append({
                    'Payload_Bytes': payload,
                    'SRAM_Mode': mode,
                    'Min_Pipeline_Depth': '-',
                    'Effective_Depth': '-',
                    'SRAM_per_ch_KB': '-',
                    'Total_SRAM_KB': '-',
                    'Bandwidth_GBps': '-',
                    'Target_Met': 'âœ—'
                })
    
    df = pd.DataFrame(results)
    
    if verbose:
        print(f"\n{'='*80}")
        print(f"  SRAM SIZING RECOMMENDATIONS")
        print(f"  Target: {target} GB/s @ {num_channels} channels, Streaming: {streaming}")
        print(f"{'='*80}\n")
        print(df.to_string(index=False))
        print(f"\n{'='*80}\n")
    
    return df


if __name__ == "__main__":
    print("\n" + "="*80)
    print("  COMPREHENSIVE SRAM SIZING ANALYSIS")
    print("="*80 + "\n")
    
    # 1. Compare modes for current design (2KB)
    print("\n1. SRAM MODE COMPARISON - Current Design (2KB payload)")
    print("-" * 80)
    compare_result = compare_sram_modes(
        payload=2048,
        pipeline_depth=4,
        num_channels=16,
        verbose=True
    )
    
    # 2. Payload vs SRAM analysis
    print("\n2. PAYLOAD vs SRAM REQUIREMENTS")
    print("-" * 80)
    payload_analysis = analyze_payload_vs_sram(
        payloads=[256, 512, 1024, 2048],
        pipeline_depths=[1, 2, 4, 8],
        num_channels=16,
        verbose=True
    )
    
    # 3. Optimal SRAM for 50 GB/s target
    print("\n3. OPTIMAL SRAM FOR 50 GB/s TARGET")
    print("-" * 80)
    optimal_2kb = find_optimal_sram_size(
        payload=2048,
        target_bandwidth=50.0,
        num_channels=16,
        streaming=True,
        verbose=True
    )
    
    # 4. Compare small payload (256B)
    print("\n4. SMALL PAYLOAD COMPARISON (256B)")
    print("-" * 80)
    small_payload = compare_sram_modes(
        payload=256,
        pipeline_depth=8,
        num_channels=16,
        verbose=True
    )
    
    # 5. Generate recommendation table
    print("\n5. COMPREHENSIVE RECOMMENDATIONS")
    print("-" * 80)
    recommendations = generate_sram_recommendation_table(
        num_channels=16,
        streaming=True,
        verbose=True
    )
    
    # Save results
    try:
        payload_analysis.to_csv('sram_payload_analysis.csv', index=False)
        recommendations.to_csv('sram_recommendations.csv', index=False)
        print(" Results saved:")
        print("  - sram_payload_analysis.csv")
        print("  - sram_recommendations.csv")
    except Exception as e:
        print(f"âœ— Could not save results: {e}")
    
    print("\n" + "="*80 + "\n")
