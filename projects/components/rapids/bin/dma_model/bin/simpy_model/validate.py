# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ValidationResult
# Purpose: Validation Framework: SimPy vs Analytical Model
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Validation Framework: SimPy vs Analytical Model

This module compares SimPy discrete-event simulation results with
the analytical performance model to validate accuracy.

Usage:
    # Validate baseline design
    results = validate_baseline()
    
    # Validate all configurations
    results = validate_all_configurations()
    
    # Generate validation report
    generate_validation_report(results)
"""

import sys
import os
from typing import Dict, List, Tuple
import pandas as pd
import numpy as np

# Add paths
try:
    from simpy_model.current_design import run_baseline_simulation, run_optimized_simulation
    from analytical.current_design import (
        get_baseline_performance,
        get_optimized_performance,
        analyze_pipelining_impact
    )
    from pyperf import AXIConfig, AXI4Performance
except ImportError:
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
    from simpy_model.current_design import run_baseline_simulation, run_optimized_simulation
    from analytical.current_design import (
        get_baseline_performance,
        get_optimized_performance,
        analyze_pipelining_impact
    )
    from pyperf import AXIConfig, AXI4Performance


class ValidationResult:
    """Container for validation comparison results."""
    
    def __init__(self, name: str, analytical: Dict, simpy: Dict):
        self.name = name
        self.analytical = analytical
        self.simpy = simpy
        self.validate()
    
    def validate(self):
        """Calculate validation metrics."""
        # Compare aggregate bandwidth
        analytical_bw = self.analytical.get('total_bw', 
                                           self.analytical.get('aggregate_bandwidth', 0))
        simpy_bw = self.simpy['aggregate_bandwidth']
        
        self.analytical_bw = analytical_bw
        self.simpy_bw = simpy_bw
        self.absolute_diff = simpy_bw - analytical_bw
        self.relative_diff_pct = (self.absolute_diff / analytical_bw) * 100 if analytical_bw else 0
        
        # Check if within tolerance
        self.tolerance_pct = 5.0  # 5% tolerance
        self.within_tolerance = abs(self.relative_diff_pct) <= self.tolerance_pct
        
        # Compare per-channel bandwidth
        if 'B_channel' in self.analytical:
            analytical_per_ch = self.analytical['B_channel']
            simpy_per_ch = self.simpy['avg_channel_bandwidth']
            self.per_channel_diff_pct = ((simpy_per_ch - analytical_per_ch) / analytical_per_ch) * 100
        else:
            self.per_channel_diff_pct = None
    
    def __repr__(self):
        status = "✓ PASS" if self.within_tolerance else "✗ FAIL"
        return (f"ValidationResult('{self.name}': {self.simpy_bw:.2f} vs {self.analytical_bw:.2f} GB/s, "
                f"diff={self.relative_diff_pct:+.1f}% [{status}])")


def validate_baseline(num_channels: int = 16,
                     simulation_time: int = 100000,
                     payload: int = 2048,
                     verbose: bool = False) -> ValidationResult:
    """
    Validate baseline configuration.
    
    Args:
        num_channels: Number of channels
        simulation_time: SimPy simulation duration
        payload: Burst size in bytes
        verbose: Print detailed comparison
    
    Returns:
        ValidationResult object
    """
    if verbose:
        print(f"\n{'='*80}")
        print(f"  VALIDATION: Baseline Configuration")
        print(f"{'='*80}\n")
        print(f"Configuration: {num_channels} channels, {payload} bytes, "
              f"{simulation_time:,} cycle simulation")
        print()
    
    # Run analytical model
    analytical = get_baseline_performance(verbose=False)
    analytical_result = analytical['performance'].calculate_channel_bandwidth(num_channels)
    
    # Run SimPy model
    simpy_result = run_baseline_simulation(
        num_channels=num_channels,
        simulation_time=simulation_time,
        payload=payload,
        verbose=False
    )
    
    # Create validation result
    result = ValidationResult("baseline", analytical_result, simpy_result)
    
    if verbose:
        print(f"Analytical Model:")
        print(f"  Aggregate BW:      {result.analytical_bw:.3f} GB/s")
        print(f"  Per-channel BW:    {analytical_result['B_channel']:.3f} GB/s")
        print(f"  Cycles per burst:  {analytical_result['cycles_per_burst']:.0f}")
        print()
        
        print(f"SimPy Model:")
        print(f"  Aggregate BW:      {result.simpy_bw:.3f} GB/s")
        print(f"  Per-channel BW:    {simpy_result['avg_channel_bandwidth']:.3f} GB/s")
        
        timing = simpy_result['timing_breakdown']
        total_timing = timing['avg_latency_cycles'] + timing['avg_data_return_cycles'] + timing['avg_drain_cycles']
        print(f"  Cycles per burst:  {total_timing:.0f}")
        print()
        
        print(f"Comparison:")
        print(f"  Difference:        {result.absolute_diff:+.3f} GB/s ({result.relative_diff_pct:+.1f}%)")
        print(f"  Within Tolerance:  {result.within_tolerance} (±{result.tolerance_pct}%)")
        print(f"  Status:            {'✓ PASS' if result.within_tolerance else '✗ FAIL'}")
        print(f"\n{'='*80}\n")
    
    return result


def validate_optimized(num_channels: int = 16,
                      simulation_time: int = 100000,
                      payload: int = 2048,
                      pipeline_depth: int = 4,
                      streaming: bool = True,
                      monolithic: bool = False,
                      verbose: bool = False) -> ValidationResult:
    """
    Validate optimized configuration.
    
    Args:
        num_channels: Number of channels
        simulation_time: SimPy simulation duration
        payload: Burst size in bytes
        pipeline_depth: Pipeline depth
        streaming: Enable streaming drain
        monolithic: Use monolithic SRAM
        verbose: Print detailed comparison
    
    Returns:
        ValidationResult object
    """
    config_name = f"optimized_p{pipeline_depth}_{'stream' if streaming else 'sf'}_{'mono' if monolithic else 'pp'}"
    
    if verbose:
        print(f"\n{'='*80}")
        print(f"  VALIDATION: {config_name}")
        print(f"{'='*80}\n")
    
    # Run analytical model
    analytical = get_optimized_performance(
        pipeline_depth=pipeline_depth,
        streaming=streaming,
        monolithic=monolithic,
        payload=payload,
        verbose=False
    )
    analytical_result = analytical['performance'].calculate_channel_bandwidth(num_channels)
    
    # Run SimPy model
    simpy_result = run_optimized_simulation(
        num_channels=num_channels,
        simulation_time=simulation_time,
        payload=payload,
        pipeline_depth=pipeline_depth,
        streaming=streaming,
        monolithic=monolithic,
        verbose=False
    )
    
    result = ValidationResult(config_name, analytical_result, simpy_result)
    
    if verbose:
        print(f"Configuration:")
        print(f"  Pipeline:    {pipeline_depth}")
        print(f"  Streaming:   {streaming}")
        print(f"  Monolithic:  {monolithic}")
        print()
        
        print(f"Analytical:  {result.analytical_bw:.3f} GB/s")
        print(f"SimPy:       {result.simpy_bw:.3f} GB/s")
        print(f"Difference:  {result.relative_diff_pct:+.1f}%")
        print(f"Status:      {'✓ PASS' if result.within_tolerance else '✗ FAIL'}")
        print(f"\n{'='*80}\n")
    
    return result


def validate_all_configurations(num_channels: int = 16,
                               simulation_time: int = 100000,
                               payload: int = 2048,
                               verbose: bool = False) -> Dict[str, ValidationResult]:
    """
    Validate multiple configurations systematically.
    
    Args:
        num_channels: Number of channels
        simulation_time: SimPy simulation duration
        payload: Burst size in bytes
        verbose: Print detailed comparison for each
    
    Returns:
        Dictionary mapping config name to ValidationResult
    """
    print(f"\n{'='*80}")
    print(f"  COMPREHENSIVE VALIDATION")
    print(f"{'='*80}")
    print(f"\nParameters: {num_channels} channels, {payload} bytes payload")
    print(f"Simulation: {simulation_time:,} cycles")
    print(f"Tolerance:  ±5%")
    print(f"\n{'='*80}\n")
    
    results = {}
    
    # Test configurations
    configs = [
        ("baseline", {
            'pipeline_depth': 1,
            'streaming': False,
            'monolithic': False
        }),
        ("pipeline_2", {
            'pipeline_depth': 2,
            'streaming': False,
            'monolithic': False
        }),
        ("pipeline_4", {
            'pipeline_depth': 4,
            'streaming': False,
            'monolithic': False
        }),
        ("streaming_only", {
            'pipeline_depth': 1,
            'streaming': True,
            'monolithic': False
        }),
        ("pipeline_plus_streaming", {
            'pipeline_depth': 4,
            'streaming': True,
            'monolithic': False
        }),
    ]
    
    for name, config in configs:
        print(f"Testing: {name}...")
        
        if name == "baseline":
            result = validate_baseline(
                num_channels=num_channels,
                simulation_time=simulation_time,
                payload=payload,
                verbose=False
            )
        else:
            result = validate_optimized(
                num_channels=num_channels,
                simulation_time=simulation_time,
                payload=payload,
                **config,
                verbose=False
            )
        
        results[name] = result
        
        status = "✓ PASS" if result.within_tolerance else "✗ FAIL"
        print(f"  Analytical: {result.analytical_bw:6.3f} GB/s")
        print(f"  SimPy:      {result.simpy_bw:6.3f} GB/s")
        print(f"  Diff:       {result.relative_diff_pct:+6.2f}%  [{status}]")
        print()
    
    return results


def generate_validation_report(results: Dict[str, ValidationResult],
                              save_csv: bool = True) -> pd.DataFrame:
    """
    Generate comprehensive validation report.
    
    Args:
        results: Dictionary from validate_all_configurations()
        save_csv: Save report to CSV file
    
    Returns:
        DataFrame with validation results
    """
    rows = []
    
    for name, result in results.items():
        rows.append({
            'Configuration': name,
            'Analytical_BW': result.analytical_bw,
            'SimPy_BW': result.simpy_bw,
            'Absolute_Diff': result.absolute_diff,
            'Relative_Diff_%': result.relative_diff_pct,
            'Within_Tolerance': result.within_tolerance,
            'Status': 'PASS' if result.within_tolerance else 'FAIL'
        })
    
    df = pd.DataFrame(rows)
    
    # Print summary
    print(f"\n{'='*80}")
    print(f"  VALIDATION REPORT")
    print(f"{'='*80}\n")
    
    print(df.to_string(index=False))
    print()
    
    # Statistics
    total_tests = len(results)
    passed = sum(1 for r in results.values() if r.within_tolerance)
    failed = total_tests - passed
    pass_rate = (passed / total_tests) * 100
    
    print(f"{'='*80}")
    print(f"  SUMMARY")
    print(f"{'='*80}")
    print(f"\nTotal Tests:     {total_tests}")
    print(f"Passed:          {passed} ({pass_rate:.1f}%)")
    print(f"Failed:          {failed}")
    print(f"\nOverall Status:  {'✓ ALL PASS' if failed == 0 else f'✗ {failed} FAILURES'}")
    print(f"\n{'='*80}\n")
    
    if save_csv:
        try:
            os.makedirs('csv', exist_ok=True)
            df.to_csv('csv/validation_report.csv', index=False)
            print("Report saved to: csv/validation_report.csv\n")
        except Exception as e:
            print(f"Could not save report: {e}\n")
    
    return df


def validate_timing_breakdown(num_channels: int = 1,
                             simulation_time: int = 100000,
                             payload: int = 2048,
                             verbose: bool = True) -> Dict:
    """
    Detailed validation of timing breakdown for single channel.
    
    This helps verify that SimPy is correctly modeling:
    - Latency phase (200 cycles)
    - Data return phase (burst_length cycles)
    - Drain phase (burst_length * cycles_per_beat)
    
    Args:
        num_channels: Should be 1 for detailed timing analysis
        simulation_time: SimPy simulation duration
        payload: Burst size in bytes
        verbose: Print detailed breakdown
    
    Returns:
        Dictionary with timing comparison
    """
    if verbose:
        print(f"\n{'='*80}")
        print(f"  TIMING BREAKDOWN VALIDATION")
        print(f"{'='*80}\n")
    
    # Analytical timing
    config = AXIConfig(
        payload=payload,
        pipeline_depth=1,
        pipelining_enabled=False,
        streaming_drain=False,
        sram_mode="pingpong"
    )
    
    latency_expected = config.latency
    data_return_expected = config.BL
    drain_expected = config.BL * config.cycles_per_beat
    total_expected = latency_expected + data_return_expected + drain_expected
    
    # SimPy timing
    simpy_result = run_baseline_simulation(
        num_channels=num_channels,
        simulation_time=simulation_time,
        payload=payload,
        verbose=False
    )
    
    timing = simpy_result['timing_breakdown']
    latency_simpy = timing['avg_latency_cycles']
    data_simpy = timing['avg_data_return_cycles']
    drain_simpy = timing['avg_drain_cycles']
    total_simpy = latency_simpy + data_simpy + drain_simpy
    
    if verbose:
        print(f"Expected (Analytical):")
        print(f"  Latency:       {latency_expected:6.1f} cycles")
        print(f"  Data Return:   {data_return_expected:6.1f} cycles")
        print(f"  Drain:         {drain_expected:6.1f} cycles")
        print(f"  TOTAL:         {total_expected:6.1f} cycles")
        print()
        
        print(f"Actual (SimPy):")
        print(f"  Latency:       {latency_simpy:6.1f} cycles")
        print(f"  Data Return:   {data_simpy:6.1f} cycles")
        print(f"  Drain:         {drain_simpy:6.1f} cycles")
        print(f"  TOTAL:         {total_simpy:6.1f} cycles")
        print()
        
        print(f"Differences:")
        print(f"  Latency:       {latency_simpy - latency_expected:+6.1f} cycles")
        print(f"  Data Return:   {data_simpy - data_return_expected:+6.1f} cycles")
        print(f"  Drain:         {drain_simpy - drain_expected:+6.1f} cycles")
        print(f"  TOTAL:         {total_simpy - total_expected:+6.1f} cycles")
        print()
        
        # Check each component
        latency_match = abs(latency_simpy - latency_expected) < 1
        data_match = abs(data_simpy - data_return_expected) < 1
        drain_match = abs(drain_simpy - drain_expected) < 1
        total_match = abs(total_simpy - total_expected) < 2
        
        print(f"Validation:")
        print(f"  Latency:       {'✓ PASS' if latency_match else '✗ FAIL'}")
        print(f"  Data Return:   {'✓ PASS' if data_match else '✗ FAIL'}")
        print(f"  Drain:         {'✓ PASS' if drain_match else '✗ FAIL'}")
        print(f"  Overall:       {'✓ PASS' if total_match else '✗ FAIL'}")
        print(f"\n{'='*80}\n")
    
    return {
        'expected': {
            'latency': latency_expected,
            'data_return': data_return_expected,
            'drain': drain_expected,
            'total': total_expected
        },
        'actual': {
            'latency': latency_simpy,
            'data_return': data_simpy,
            'drain': drain_simpy,
            'total': total_simpy
        },
        'valid': {
            'latency': abs(latency_simpy - latency_expected) < 1,
            'data_return': abs(data_simpy - data_return_expected) < 1,
            'drain': abs(drain_simpy - drain_expected) < 1,
            'total': abs(total_simpy - total_expected) < 2
        }
    }


if __name__ == "__main__":
    print("\n" + "="*80)
    print("  SIMPY MODEL VALIDATION SUITE")
    print("="*80 + "\n")
    
    # 1. Validate timing breakdown (single channel)
    print("1. TIMING BREAKDOWN (Single Channel)")
    print("-" * 80)
    timing_validation = validate_timing_breakdown(
        num_channels=1,
        simulation_time=100000,
        verbose=True
    )
    
    # 2. Validate baseline (16 channels)
    print("\n2. BASELINE CONFIGURATION (16 Channels)")
    print("-" * 80)
    baseline_validation = validate_baseline(
        num_channels=16,
        simulation_time=100000,
        verbose=True
    )
    
    # 3. Validate all configurations
    print("\n3. COMPREHENSIVE VALIDATION")
    print("-" * 80)
    all_results = validate_all_configurations(
        num_channels=16,
        simulation_time=100000,
        verbose=False
    )
    
    # 4. Generate report
    report = generate_validation_report(all_results, save_csv=True)
    
    print("\nValidation complete!")
