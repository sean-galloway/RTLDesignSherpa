# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ReadChannelConfig
# Purpose: SimPy Discrete-Event Simulation: AXI4 Read Path
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
SimPy Discrete-Event Simulation: AXI4 Read Path

Core simulation model for read path with baseline and optimized configurations.

CRITICAL FIX: Timing breakdown now correctly calculates per-channel averages
instead of dividing by total bursts across all channels.

Usage:
    from simpy_model.current_design import run_baseline_simulation
    
    results = run_baseline_simulation(num_channels=16, simulation_time=100000)
    print(f"Bandwidth: {results['aggregate_bandwidth']:.2f} GB/s")
    print(f"Timing: {results['timing_breakdown']}")
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
class ReadChannelConfig:
    """Configuration for a single read channel."""
    channel_id: int
    payload: int = 2048  # Burst size in bytes
    bus_width: int = DEFAULT_W  # 64 bytes per beat
    frequency: float = DEFAULT_F  # 1 GHz
    alpha: float = DEFAULT_ALPHA  # Protocol efficiency
    latency: int = DEFAULT_LATENCY  # Memory latency in cycles
    cycles_per_beat: int = 16  # Custom side drain rate
    per_channel_cap: float = 4.0  # GB/s per channel
    
    # SRAM configuration
    sram_mode: str = "pingpong"  # "pingpong" or "monolithic"
    total_sram_size: int = 4096  # Total SRAM per channel (bytes)
    sram_slot_size: int = 2048  # Size of each ping-pong slot (bytes)
    
    # Drain mode
    streaming_drain: bool = False  # True = streaming, False = store-and-forward
    
    # Pipelining
    pipeline_depth: int = 1
    pipelining_enabled: bool = False
    
    def __post_init__(self):
        """Calculate derived parameters."""
        self.burst_length = self.payload // self.bus_width  # beats
        self.drain_cycles = self.burst_length * self.cycles_per_beat
        self.axi_peak_bw = self.bus_width * self.frequency * self.alpha  # GB/s
        
        # SRAM pipeline limit
        if self.sram_mode == "pingpong":
            self.max_sram_pipeline = 2
        else:  # monolithic
            self.max_sram_pipeline = self.total_sram_size // self.payload
        
        # Effective pipeline depth
        self.effective_pipeline = min(self.pipeline_depth, self.max_sram_pipeline)


@dataclass
class ReadChannelStats:
    """Statistics for a single read channel."""
    channel_id: int
    bursts_completed: int = 0
    bytes_transferred: int = 0
    total_cycles_active: int = 0
    last_completion_time: float = 0
    
    # Timing breakdown
    time_in_latency: float = 0
    time_in_data_return: float = 0
    time_in_drain: float = 0
    time_idle: float = 0
    
    # SRAM occupancy tracking
    sram_occupancy_samples: List[int] = field(default_factory=list)
    sram_sample_times: List[float] = field(default_factory=list)


class ReadChannel:
    """
    Simulates a single read channel with store-and-forward drain.
    
    State machine:
        IDLE → WAITING_LATENCY → RECEIVING_DATA → DRAINING → IDLE
    
    With pipelining enabled, can have multiple bursts in flight,
    but each still goes through full cycle.
    """
    
    def __init__(self, env: simpy.Environment, config: ReadChannelConfig,
                 axi_bandwidth: simpy.Resource, stats: ReadChannelStats):
        self.env = env
        self.config = config
        self.axi = axi_bandwidth
        self.stats = stats
        
        # SRAM resources
        if config.sram_mode == "pingpong":
            # Ping-pong: 2 slots, track which is in use
            self.sram_slots = simpy.Resource(env, capacity=2)
            self.slot_size = config.sram_slot_size
        else:
            # Monolithic: track bytes used
            self.sram_bytes_used = 0
            self.sram_capacity = config.total_sram_size
        
        # Pipeline tracking
        self.bursts_in_flight = 0
        self.max_pipeline = config.effective_pipeline
        
        # Start the channel process
        self.process = env.process(self.run())
    
    def run(self):
        """Main channel process - issues read bursts."""
        while True:
            # Wait if we've hit pipeline limit
            while self.bursts_in_flight >= self.max_pipeline:
                yield self.env.timeout(1)
            
            # Check SRAM availability
            if self.config.sram_mode == "pingpong":
                # Need a free slot
                if self.sram_slots.count >= self.sram_slots.capacity:
                    yield self.env.timeout(1)
                    continue
            else:
                # Need enough free bytes
                if self.sram_bytes_used + self.config.payload > self.sram_capacity:
                    yield self.env.timeout(1)
                    continue
            
            # Issue a burst
            self.bursts_in_flight += 1
            self.env.process(self.process_burst())
            
            # If no pipelining, wait for burst to complete
            if not self.config.pipelining_enabled:
                while self.bursts_in_flight > 0:
                    yield self.env.timeout(1)
    
    def process_burst(self):
        """Process a single burst through the pipeline."""
        start_time = self.env.now
        
        # Reserve SRAM
        if self.config.sram_mode == "pingpong":
            slot_request = self.sram_slots.request()
            yield slot_request
        else:
            self.sram_bytes_used += self.config.payload
        
        # Phase 1: Latency
        latency_start = self.env.now
        yield self.env.timeout(self.config.latency)
        self.stats.time_in_latency += self.env.now - latency_start
        
        # Phase 2: Data Return (over AXI)
        # Request AXI bandwidth for data return
        # Account for protocol efficiency (alpha)
        # Effective rate: 64 bytes/beat * alpha = 57.6 bytes/cycle
        # Time = beats / (alpha beats/cycle) = beats / alpha cycles
        data_start = self.env.now
        with self.axi.request() as req:
            yield req
            # Data arrives at effective rate considering protocol efficiency
            # At alpha=0.9: 32 beats / 0.9 = 35.6 cycles (not 32!)
            effective_data_return_cycles = self.config.burst_length / self.config.alpha
            yield self.env.timeout(effective_data_return_cycles)
        self.stats.time_in_data_return += self.env.now - data_start
        
        # Phase 3: Drain
        drain_start = self.env.now

        # CRITICAL FIX: Drain behavior depends on BOTH streaming mode AND pipelining
        if self.config.pipelining_enabled and self.config.pipeline_depth > 1:
            # WITH PIPELINING: Drain overlaps with next burst fetch
            # The drain happens "in the background" while we issue the next read request
            # From a timing perspective, this is accounted for by NOT waiting here
            # The throughput becomes limited by: latency + data_return (drain hidden)
            if self.config.streaming_drain:
                # Streaming + Pipeline: Best case - drain completely overlapped
                # No additional wait needed (drain happens concurrently with next burst)
                pass  # No timeout needed
            else:
                # Store-and-Forward + Pipeline: Still need to wait for data to arrive
                # But drain then overlaps with next burst
                # This case is unusual (why pipeline without streaming?)
                # For correctness: wait for data return, then drain overlaps
                pass  # Data return already happened above, drain overlaps with next

            # In both pipeline cases, we track drain time for statistics but don't block
            self.stats.time_in_drain += self.config.drain_cycles
        else:
            # WITHOUT PIPELINING: Must complete full drain before next burst
            if self.config.streaming_drain:
                # Streaming (no pipeline): Drain overlaps with data return
                # We already waited for data return above (35.6 cycles)
                # Now wait for remaining drain time
                remaining_drain = max(0, self.config.drain_cycles - effective_data_return_cycles)
                yield self.env.timeout(remaining_drain)
                self.stats.time_in_drain += remaining_drain
            else:
                # Store-and-Forward (no pipeline): Wait for ALL data to arrive, THEN drain
                # This is the current design - data return already happened above,
                # now we drain the full burst
                yield self.env.timeout(self.config.drain_cycles)
                self.stats.time_in_drain += self.config.drain_cycles
        
        # Release SRAM
        if self.config.sram_mode == "pingpong":
            self.sram_slots.release(slot_request)
        else:
            self.sram_bytes_used -= self.config.payload
        
        # Update statistics
        self.bursts_in_flight -= 1
        self.stats.bursts_completed += 1
        self.stats.bytes_transferred += self.config.payload
        self.stats.last_completion_time = self.env.now
        self.stats.total_cycles_active += self.env.now - start_time


class AXI4ReadSystem:
    """
    Complete AXI4 read system with multiple independent channels.
    
    Models:
    - Multiple read channels operating independently
    - Shared AXI bandwidth (peak capacity)
    - Per-channel drain rate limits
    - SRAM buffering per channel
    """
    
    def __init__(self, env: simpy.Environment, num_channels: int,
                 channel_config: ReadChannelConfig,
                 axi_peak_bandwidth: float = 57.6):
        """
        Initialize the system.
        
        Args:
            env: SimPy environment
            num_channels: Number of concurrent read channels
            channel_config: Configuration template for channels
            axi_peak_bandwidth: Peak AXI bandwidth in GB/s
        """
        self.env = env
        self.num_channels = num_channels
        self.channel_config = channel_config
        
        # Shared AXI bandwidth resource
        # Model as resource with high capacity (many concurrent users)
        # Actual bandwidth limit enforced by timing
        self.axi_bandwidth = simpy.Resource(env, capacity=num_channels)
        
        # Create channels
        self.channels = []
        self.channel_stats = []
        
        for i in range(num_channels):
            config = ReadChannelConfig(
                channel_id=i,
                payload=channel_config.payload,
                bus_width=channel_config.bus_width,
                frequency=channel_config.frequency,
                latency=channel_config.latency,
                cycles_per_beat=channel_config.cycles_per_beat,
                per_channel_cap=channel_config.per_channel_cap,
                sram_mode=channel_config.sram_mode,
                total_sram_size=channel_config.total_sram_size,
                sram_slot_size=channel_config.sram_slot_size,
                streaming_drain=channel_config.streaming_drain,
                pipeline_depth=channel_config.pipeline_depth,
                pipelining_enabled=channel_config.pipelining_enabled
            )
            
            stats = ReadChannelStats(channel_id=i)
            channel = ReadChannel(env, config, self.axi_bandwidth, stats)
            
            self.channels.append(channel)
            self.channel_stats.append(stats)
    
    def get_aggregate_statistics(self, simulation_time: float) -> Dict:
        """
        Calculate aggregate statistics across all channels.
        
        CRITICAL FIX: Timing breakdown now correctly calculated per-channel first,
        then averaged, instead of dividing by total_bursts across all channels.
        
        Args:
            simulation_time: Total simulation time in cycles
        
        Returns:
            Dictionary with aggregate statistics
        """
        total_bursts = sum(s.bursts_completed for s in self.channel_stats)
        total_bytes = sum(s.bytes_transferred for s in self.channel_stats)
        
        # Calculate raw bandwidth (GB/s)
        # bytes / cycles * frequency (GHz) = GB/s
        if simulation_time > 0:
            raw_bandwidth = (total_bytes / simulation_time) * self.channel_config.frequency
        else:
            raw_bandwidth = 0
        
        # Apply system-wide limits (same as analytical model)
        # 1. Per-channel capacity limit
        max_channels_by_drain = int(
            (self.channel_config.per_channel_cap * self.num_channels * simulation_time) / 
            (total_bytes * self.channel_config.frequency)
        ) if total_bytes > 0 else self.num_channels
        
        # 2. AXI peak bandwidth
        axi_peak = self.channel_config.axi_peak_bw
        
        # 3. Total custom side capacity
        total_custom_cap = self.channel_config.per_channel_cap * self.num_channels
        
        # Aggregate bandwidth is minimum of these limits
        aggregate_bandwidth = min(raw_bandwidth, axi_peak, total_custom_cap)
        
        # Determine limiting factor
        if aggregate_bandwidth >= axi_peak * 0.99:
            limited_by = "AXI_peak"
        elif aggregate_bandwidth >= total_custom_cap * 0.99:
            limited_by = "custom_side_capacity"
        else:
            limited_by = "timing"
        
        # Per-channel statistics
        per_channel_bursts = [s.bursts_completed for s in self.channel_stats]
        per_channel_bytes = [s.bytes_transferred for s in self.channel_stats]
        per_channel_bw = [(b / simulation_time) * self.channel_config.frequency 
                         if simulation_time > 0 else 0 
                         for b in per_channel_bytes]
        
        # =====================================================================
        # CRITICAL FIX: Calculate timing breakdown correctly!
        # =====================================================================
        # OLD (WRONG): Divide total time by total bursts across all channels
        # NEW (CORRECT): Calculate per-channel average, then average across channels
        
        # Calculate per-channel average cycles per burst
        per_channel_avg_latency = []
        per_channel_avg_data_return = []
        per_channel_avg_drain = []
        
        for stats in self.channel_stats:
            if stats.bursts_completed > 0:
                per_channel_avg_latency.append(stats.time_in_latency / stats.bursts_completed)
                per_channel_avg_data_return.append(stats.time_in_data_return / stats.bursts_completed)
                per_channel_avg_drain.append(stats.time_in_drain / stats.bursts_completed)
        
        # Average across channels (all channels should have similar timing)
        avg_latency_cycles = np.mean(per_channel_avg_latency) if per_channel_avg_latency else 0
        avg_data_return_cycles = np.mean(per_channel_avg_data_return) if per_channel_avg_data_return else 0
        avg_drain_cycles = np.mean(per_channel_avg_drain) if per_channel_avg_drain else 0
        
        # =====================================================================
        # End of fix
        # =====================================================================
        
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
                'total_custom_cap': total_custom_cap,
                'per_channel_cap': self.channel_config.per_channel_cap
            },
            'timing_breakdown': {
                'avg_latency_cycles': avg_latency_cycles,
                'avg_data_return_cycles': avg_data_return_cycles,
                'avg_drain_cycles': avg_drain_cycles,
            },
            'config': {
                'payload': self.channel_config.payload,
                'pipeline_depth': self.channel_config.pipeline_depth,
                'pipelining_enabled': self.channel_config.pipelining_enabled,
                'streaming_drain': self.channel_config.streaming_drain,
                'sram_mode': self.channel_config.sram_mode,
            }
        }


def run_baseline_simulation(num_channels: int = 16,
                           simulation_time: int = 100000,
                           payload: int = 2048,
                           verbose: bool = False) -> Dict:
    """
    Run baseline simulation with current design parameters.
    
    Args:
        num_channels: Number of concurrent read channels
        simulation_time: Simulation duration in cycles
        payload: Burst size in bytes
        verbose: Print detailed progress
    
    Returns:
        Dictionary with simulation results and statistics
    """
    # Create SimPy environment
    env = simpy.Environment()
    
    # Configure baseline: no pipelining, store-and-forward, ping-pong SRAM
    config = ReadChannelConfig(
        channel_id=0,  # Will be overridden per channel
        payload=payload,
        pipeline_depth=1,
        pipelining_enabled=False,
        streaming_drain=False,  # Store-and-forward
        sram_mode="pingpong"
    )
    
    if verbose:
        print(f"\n{'='*80}")
        print(f"  SIMPY SIMULATION: Baseline (Current Design) - READ PATH")
        print(f"{'='*80}")
        print(f"\nConfiguration:")
        print(f"  Channels:           {num_channels}")
        print(f"  Payload:            {payload} bytes (read burst)")
        print(f"  Simulation Time:    {simulation_time:,} cycles")
        print(f"  Pipeline:           {config.pipeline_depth} (no pipelining)")
        print(f"  Drain Mode:         Store-and-Forward")
        print(f"  SRAM Mode:          Ping-Pong")
        print(f"\nRunning simulation...")
    
    # Create system
    system = AXI4ReadSystem(env, num_channels, config)
    
    # Run simulation
    env.run(until=simulation_time)
    
    # Collect results
    results = system.get_aggregate_statistics(simulation_time)
    
    if verbose:
        print(f"Complete!\n")
        print(f"Results (Read Path):")
        print(f"  Total Bursts:       {results['total_bursts']:,}")
        print(f"  Total Data:         {results['total_bytes'] / 1e9:.3f} GB")
        print(f"  Aggregate Read BW:  {results['aggregate_bandwidth']:.3f} GB/s")
        print(f"  Avg Channel BW:     {results['avg_channel_bandwidth']:.3f} GB/s")
        print(f"\nTiming Breakdown (avg per burst):")
        print(f"  Latency:            {results['timing_breakdown']['avg_latency_cycles']:.1f} cycles")
        print(f"  Data Return:        {results['timing_breakdown']['avg_data_return_cycles']:.1f} cycles")
        print(f"  Drain:              {results['timing_breakdown']['avg_drain_cycles']:.1f} cycles")
        total_avg = sum(results['timing_breakdown'].values())
        print(f"  TOTAL:              {total_avg:.1f} cycles")
        print(f"{'='*80}\n")
    
    return results


def run_optimized_simulation(num_channels: int = 16,
                            simulation_time: int = 100000,
                            payload: int = 2048,
                            pipeline_depth: int = 4,
                            streaming: bool = True,
                            monolithic: bool = False,
                            verbose: bool = False) -> Dict:
    """
    Run simulation with optimizations enabled.
    
    Args:
        num_channels: Number of concurrent read channels
        simulation_time: Simulation duration in cycles
        payload: Burst size in bytes
        pipeline_depth: Pipeline depth (>1 for pipelining)
        streaming: Enable streaming drain
        monolithic: Use monolithic SRAM instead of ping-pong
        verbose: Print detailed progress
    
    Returns:
        Dictionary with simulation results and statistics
    """
    env = simpy.Environment()
    
    sram_mode = "monolithic" if monolithic else "pingpong"
    
    config = ReadChannelConfig(
        channel_id=0,
        payload=payload,
        pipeline_depth=pipeline_depth,
        pipelining_enabled=(pipeline_depth > 1),
        streaming_drain=streaming,
        sram_mode=sram_mode
    )
    
    if verbose:
        print(f"\n{'='*80}")
        print(f"  SIMPY SIMULATION: Optimized Design - READ PATH")
        print(f"{'='*80}")
        print(f"\nConfiguration:")
        print(f"  Channels:           {num_channels}")
        print(f"  Payload:            {payload} bytes (read burst)")
        print(f"  Simulation Time:    {simulation_time:,} cycles")
        print(f"  Pipeline Depth:     {pipeline_depth}")
        print(f"  Drain Mode:         {'Streaming' if streaming else 'Store-and-Forward'}")
        print(f"  SRAM Mode:          {sram_mode.title()}")
        print(f"  SRAM Limit:         {config.max_sram_pipeline} bursts")
        print(f"\nRunning simulation...")
    
    system = AXI4ReadSystem(env, num_channels, config)
    env.run(until=simulation_time)
    results = system.get_aggregate_statistics(simulation_time)
    
    if verbose:
        print(f"Complete!\n")
        print(f"Results (Read Path):")
        print(f"  Total Bursts:       {results['total_bursts']:,}")
        print(f"  Aggregate Read BW:  {results['aggregate_bandwidth']:.3f} GB/s")
        print(f"  Avg Channel BW:     {results['avg_channel_bandwidth']:.3f} GB/s")
        print(f"{'='*80}\n")
    
    return results


if __name__ == "__main__":
    print("\n" + "="*80)
    print("  SIMPY DISCRETE-EVENT SIMULATION")
    print("  AXI4 Read Path Performance")
    print("="*80)
    
    # Run baseline
    print("\n1. BASELINE (Current Design) - READ PATH")
    print("-" * 80)
    baseline = run_baseline_simulation(
        num_channels=16,
        simulation_time=100000,
        payload=2048,
        verbose=True
    )
    
    # Run optimized
    print("\n2. OPTIMIZED (Pipeline + Streaming) - READ PATH")
    print("-" * 80)
    optimized = run_optimized_simulation(
        num_channels=16,
        simulation_time=100000,
        payload=2048,
        pipeline_depth=4,
        streaming=True,
        monolithic=False,
        verbose=True
    )
    
    # Compare
    print("\n3. COMPARISON - READ BANDWIDTH")
    print("-" * 80)
    improvement = ((optimized['aggregate_bandwidth'] / baseline['aggregate_bandwidth']) - 1) * 100
    print(f"\nBaseline:    {baseline['aggregate_bandwidth']:.2f} GB/s")
    print(f"Optimized:   {optimized['aggregate_bandwidth']:.2f} GB/s")
    print(f"Improvement: +{improvement:.1f}%")
    print(f"\nTarget:      {'✓ MET' if optimized['aggregate_bandwidth'] >= 50 else '✗ NOT MET'} (50+ GB/s)")
    print("\n" + "="*80 + "\n")
