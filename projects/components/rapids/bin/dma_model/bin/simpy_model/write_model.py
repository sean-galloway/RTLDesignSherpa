# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: WriteChannelConfig
# Purpose: SimPy Discrete-Event Simulation: AXI4 Write Path
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
SimPy Discrete-Event Simulation: AXI4 Write Path

This module provides discrete-event simulation of the write path to complement
the read path simulation in current_design.py.

Write path characteristics:
- Smaller bursts: 256 bytes (4 beats @ 64 bytes/beat)
- Outstanding burst limit: 32 system-wide
- Custom side fills buffer → AXI writes to memory
- No drain phase (writes go directly to memory)

Usage:
    from simpy_model.write_design import run_write_simulation
    
    results = run_write_simulation(num_channels=16, simulation_time=100000)
"""

import simpy
import numpy as np
from dataclasses import dataclass, field
from typing import List, Dict
import sys
import os

# Add pyperf to path if needed
try:
    from pyperf import DEFAULT_W, DEFAULT_F, DEFAULT_ALPHA, DEFAULT_LATENCY
except ImportError:
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
    from pyperf import DEFAULT_W, DEFAULT_F, DEFAULT_ALPHA, DEFAULT_LATENCY


@dataclass
class WriteChannelConfig:
    """Configuration for a single write channel."""
    channel_id: int
    payload: int = 256  # Write burst size in bytes
    bus_width: int = DEFAULT_W  # 64 bytes per beat
    frequency: float = DEFAULT_F  # 1 GHz
    alpha: float = DEFAULT_ALPHA  # Protocol efficiency
    latency: int = DEFAULT_LATENCY  # Memory latency in cycles
    
    def __post_init__(self):
        """Calculate derived parameters."""
        self.burst_length = self.payload // self.bus_width  # beats
        self.axi_peak_bw = self.bus_width * self.frequency * self.alpha  # GB/s


@dataclass
class WriteChannelStats:
    """Statistics for a single write channel."""
    channel_id: int
    bursts_completed: int = 0
    bytes_transferred: int = 0
    total_cycles_active: int = 0
    last_completion_time: float = 0
    
    # Timing breakdown
    time_in_latency: float = 0
    time_in_data_send: float = 0


class WriteChannel:
    """
    Simulates a single write channel.
    
    State machine:
        IDLE → FILLING → WAITING_LATENCY → SENDING_DATA → IDLE
    
    Limited by system-wide outstanding burst resource.
    """
    
    def __init__(self, env: simpy.Environment, config: WriteChannelConfig,
                 outstanding_bursts: simpy.Resource, stats: WriteChannelStats):
        self.env = env
        self.config = config
        self.outstanding = outstanding_bursts
        self.stats = stats
        
        # Start the channel process
        self.process = env.process(self.run())
    
    def run(self):
        """Main channel process - issues write bursts."""
        while True:
            # Request outstanding burst slot
            with self.outstanding.request() as req:
                yield req
                
                # Process burst
                yield self.env.process(self.process_burst())
    
    def process_burst(self):
        """Process a single write burst."""
        start_time = self.env.now
        
        # Phase 1: Fill from custom side (assume instant for modeling)
        # In reality, data comes from custom side, but we model this as available
        
        # Phase 2: Write request + Latency
        latency_start = self.env.now
        yield self.env.timeout(self.config.latency)
        self.stats.time_in_latency += self.env.now - latency_start
        
        # Phase 3: Send Data over AXI
        data_start = self.env.now
        # Account for protocol efficiency
        effective_data_send_cycles = self.config.burst_length / self.config.alpha
        yield self.env.timeout(effective_data_send_cycles)
        self.stats.time_in_data_send += self.env.now - data_start
        
        # Update statistics
        self.stats.bursts_completed += 1
        self.stats.bytes_transferred += self.config.payload
        self.stats.last_completion_time = self.env.now
        self.stats.total_cycles_active += self.env.now - start_time


class AXI4WriteSystem:
    """
    Complete AXI4 write system with multiple channels.
    
    Models:
    - Multiple write channels operating independently
    - Shared outstanding burst limit (system-wide)
    - AXI bandwidth sharing
    """
    
    def __init__(self, env: simpy.Environment, num_channels: int,
                 channel_config: WriteChannelConfig,
                 max_outstanding_bursts: int = 32):
        """
        Initialize the system.
        
        Args:
            env: SimPy environment
            num_channels: Number of write channels
            channel_config: Configuration template
            max_outstanding_bursts: System-wide outstanding burst limit
        """
        self.env = env
        self.num_channels = num_channels
        self.channel_config = channel_config
        self.max_outstanding = max_outstanding_bursts
        
        # Shared outstanding burst resource
        self.outstanding_bursts = simpy.Resource(env, capacity=max_outstanding_bursts)
        
        # Create channels
        self.channels = []
        self.channel_stats = []
        
        for i in range(num_channels):
            config = WriteChannelConfig(
                channel_id=i,
                payload=channel_config.payload,
                bus_width=channel_config.bus_width,
                frequency=channel_config.frequency,
                latency=channel_config.latency
            )
            
            stats = WriteChannelStats(channel_id=i)
            channel = WriteChannel(env, config, self.outstanding_bursts, stats)
            
            self.channels.append(channel)
            self.channel_stats.append(stats)
    
    def get_aggregate_statistics(self, simulation_time: float) -> Dict:
        """
        Calculate aggregate statistics.
        
        Args:
            simulation_time: Total simulation time in cycles
        
        Returns:
            Dictionary with aggregate statistics
        """
        total_bursts = sum(s.bursts_completed for s in self.channel_stats)
        total_bytes = sum(s.bytes_transferred for s in self.channel_stats)
        
        # Calculate raw bandwidth
        if simulation_time > 0:
            raw_bandwidth = (total_bytes / simulation_time) * self.channel_config.frequency
        else:
            raw_bandwidth = 0
        
        # Apply system limits
        axi_peak = self.channel_config.axi_peak_bw
        aggregate_bandwidth = min(raw_bandwidth, axi_peak)
        
        # Determine limiting factor
        if aggregate_bandwidth == axi_peak:
            limited_by = "AXI_peak"
        else:
            limited_by = "outstanding_bursts"
        
        # Per-channel statistics
        per_channel_bursts = [s.bursts_completed for s in self.channel_stats]
        per_channel_bytes = [s.bytes_transferred for s in self.channel_stats]
        per_channel_bw = [(b / simulation_time) * self.channel_config.frequency 
                         if simulation_time > 0 else 0 
                         for b in per_channel_bytes]
        
        # Timing breakdown
        avg_latency_time = np.mean([s.time_in_latency for s in self.channel_stats])
        avg_data_time = np.mean([s.time_in_data_send for s in self.channel_stats])
        
        return {
            'num_channels': self.num_channels,
            'simulation_time': simulation_time,
            'total_bursts': total_bursts,
            'total_bytes': total_bytes,
            'raw_bandwidth': raw_bandwidth,
            'aggregate_bandwidth': aggregate_bandwidth,
            'limited_by': limited_by,
            'per_channel_bandwidth': per_channel_bw,
            'avg_channel_bandwidth': np.mean(per_channel_bw) if per_channel_bw else 0,
            'per_channel_bursts': per_channel_bursts,
            'system_limits': {
                'axi_peak': axi_peak,
                'max_outstanding': self.max_outstanding,
                'outstanding_per_channel': self.max_outstanding / self.num_channels
            },
            'timing_breakdown': {
                'avg_latency_cycles': avg_latency_time / total_bursts if total_bursts > 0 else 0,
                'avg_data_send_cycles': avg_data_time / total_bursts if total_bursts > 0 else 0,
            },
            'config': {
                'payload': self.channel_config.payload,
                'max_outstanding': self.max_outstanding,
            }
        }


def run_write_simulation(num_channels: int = 16,
                        simulation_time: int = 100000,
                        payload: int = 256,
                        max_outstanding: int = 32,
                        verbose: bool = False) -> Dict:
    """
    Run write path simulation.
    
    Args:
        num_channels: Number of write channels
        simulation_time: Simulation duration in cycles
        payload: Write burst size in bytes
        max_outstanding: System-wide outstanding burst limit
        verbose: Print detailed progress
    
    Returns:
        Dictionary with simulation results
    """
    # Create SimPy environment
    env = simpy.Environment()
    
    # Configure channel
    config = WriteChannelConfig(
        channel_id=0,
        payload=payload
    )
    
    if verbose:
        print(f"\n{'='*80}")
        print(f"  SIMPY SIMULATION: Write Path")
        print(f"{'='*80}")
        print(f"\nConfiguration:")
        print(f"  Channels:           {num_channels}")
        print(f"  Payload:            {payload} bytes (write burst)")
        print(f"  Simulation Time:    {simulation_time:,} cycles")
        print(f"  Max Outstanding:    {max_outstanding} (system-wide)")
        print(f"  Outstanding/Ch:     {max_outstanding / num_channels:.1f}")
        print(f"\nRunning simulation...")
    
    # Create system
    system = AXI4WriteSystem(env, num_channels, config, max_outstanding)
    
    # Run simulation
    env.run(until=simulation_time)
    
    # Collect results
    results = system.get_aggregate_statistics(simulation_time)
    
    if verbose:
        print(f"Complete!\n")
        print(f"Results (Write Path):")
        print(f"  Total Bursts:       {results['total_bursts']:,}")
        print(f"  Total Data:         {results['total_bytes'] / 1e9:.3f} GB")
        print(f"  Aggregate Write BW: {results['aggregate_bandwidth']:.3f} GB/s")
        print(f"  Avg Channel BW:     {results['avg_channel_bandwidth']:.3f} GB/s")
        print(f"\nTiming Breakdown (avg per burst):")
        print(f"  Latency:            {results['timing_breakdown']['avg_latency_cycles']:.1f} cycles")
        print(f"  Data Send:          {results['timing_breakdown']['avg_data_send_cycles']:.1f} cycles")
        total_avg = sum(results['timing_breakdown'].values())
        print(f"  TOTAL:              {total_avg:.1f} cycles")
        print(f"{'='*80}\n")
    
    return results


def run_optimized_write_simulation(num_channels: int = 16,
                                  simulation_time: int = 100000,
                                  payload: int = 256,
                                  max_outstanding: int = 64,
                                  verbose: bool = False) -> Dict:
    """
    Run optimized write simulation with increased outstanding limit.
    
    Args:
        num_channels: Number of write channels
        simulation_time: Simulation duration in cycles
        payload: Write burst size in bytes
        max_outstanding: Increased outstanding burst limit
        verbose: Print detailed progress
    
    Returns:
        Dictionary with simulation results
    """
    env = simpy.Environment()
    
    config = WriteChannelConfig(
        channel_id=0,
        payload=payload
    )
    
    if verbose:
        print(f"\n{'='*80}")
        print(f"  SIMPY SIMULATION: Optimized Write Path")
        print(f"{'='*80}")
        print(f"\nConfiguration:")
        print(f"  Channels:           {num_channels}")
        print(f"  Payload:            {payload} bytes")
        print(f"  Simulation Time:    {simulation_time:,} cycles")
        print(f"  Max Outstanding:    {max_outstanding} (increased from 32)")
        print(f"\nRunning simulation...")
    
    system = AXI4WriteSystem(env, num_channels, config, max_outstanding)
    env.run(until=simulation_time)
    results = system.get_aggregate_statistics(simulation_time)
    
    if verbose:
        print(f"Complete!\n")
        print(f"Results (Write Path):")
        print(f"  Total Bursts:       {results['total_bursts']:,}")
        print(f"  Aggregate Write BW: {results['aggregate_bandwidth']:.3f} GB/s")
        print(f"{'='*80}\n")
    
    return results


if __name__ == "__main__":
    print("\n" + "="*80)
    print("  SIMPY WRITE PATH SIMULATION")
    print("="*80)
    
    # Run baseline write
    print("\n1. BASELINE WRITE")
    print("-" * 80)
    baseline_write = run_write_simulation(
        num_channels=16,
        simulation_time=100000,
        payload=256,
        max_outstanding=32,
        verbose=True
    )
    
    # Run optimized write
    print("\n2. OPTIMIZED WRITE (Increased Outstanding)")
    print("-" * 80)
    optimized_write = run_optimized_write_simulation(
        num_channels=16,
        simulation_time=100000,
        payload=256,
        max_outstanding=64,
        verbose=True
    )
    
    # Compare
    print("\n3. COMPARISON - WRITE BANDWIDTH")
    print("-" * 80)
    improvement = ((optimized_write['aggregate_bandwidth'] / baseline_write['aggregate_bandwidth']) - 1) * 100
    print(f"\nBaseline:    {baseline_write['aggregate_bandwidth']:.2f} GB/s")
    print(f"Optimized:   {optimized_write['aggregate_bandwidth']:.2f} GB/s")
    print(f"Improvement: +{improvement:.1f}%")
    print("\n" + "="*80 + "\n")
