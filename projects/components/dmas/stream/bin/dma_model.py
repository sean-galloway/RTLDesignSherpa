#!/usr/bin/env python3
"""
DMA Performance Model for V1/V2/V3 AXI Read/Write Engines

Purpose: Analytical model to predict sustained bandwidth based on:
         - Memory latency (cycles)
         - Burst length (beats per transaction)
         - Data width (bits per beat)
         - Queue depth (V2/V3 only)
         - Outstanding transactions (V2/V3 only)

Author: RTL Design Sherpa
Created: 2025-10-28
"""

import argparse
from typing import Dict, Tuple


def v1_bandwidth_model(latency: int, burst_len: int) -> Tuple[float, Dict]:
    """
    V1 bandwidth model - Single outstanding transaction.

    V1 Timeline for one burst:
    - 1 cycle: AR/AW handshake (command issue)
    - latency cycles: Wait for first R/W beat
    - burst_len cycles: Receive R beats / Send W beats + B response
    - 1 cycle: Completion strobe (datard_done_strobe / datawr_done_strobe)

    Args:
        latency: Memory latency in cycles (AR→first R, or AW→B)
        burst_len: Burst length in beats

    Returns:
        (bandwidth_beats_per_cycle, debug_info)
    """
    # V1 must wait for each transaction to complete before issuing next
    cycles_per_burst = 1 + latency + burst_len + 1
    beats_per_burst = burst_len

    bandwidth = beats_per_burst / cycles_per_burst

    debug_info = {
        'model': 'V1 (single outstanding)',
        'ar_aw_cycles': 1,
        'latency_cycles': latency,
        'data_cycles': burst_len,
        'completion_cycles': 1,
        'total_cycles_per_burst': cycles_per_burst,
        'beats_per_burst': beats_per_burst,
        'bandwidth_beats_per_cycle': bandwidth,
        'efficiency_percent': bandwidth * 100
    }

    return bandwidth, debug_info


def v2_bandwidth_model(latency: int, burst_len: int, queue_depth: int,
                       num_commands: int = 1000) -> Tuple[float, Dict]:
    """
    V2 bandwidth model - Command pipelined with queue.

    V2 uses command queue to hide latency. In steady state, achieves
    near-ideal throughput (1 beat/cycle) if:
    - Queue depth ≥ latency / burst_len
    - Sufficient outstanding transactions

    Startup Phase:
    - Fill command queue (queue_depth commands × 1 cycle each)
    - Wait for first data to arrive (latency cycles)

    Steady State:
    - 1 beat per cycle (assuming no backpressure)

    Args:
        latency: Memory latency in cycles
        burst_len: Burst length in beats
        queue_depth: Command queue depth
        num_commands: Total commands to model (default 1000 for sustained BW)

    Returns:
        (bandwidth_beats_per_cycle, debug_info)
    """
    # Startup: Issue queue_depth commands, wait for first data
    startup_issue_cycles = queue_depth  # 1 cycle per command issue
    startup_latency_cycles = latency    # Wait for first R beat

    # Steady state: Ideal = 1 beat/cycle
    # Reality: Depends on queue depth vs latency
    #   - If queue_depth * burst_len > latency: Fully pipelined (1 beat/cycle)
    #   - Otherwise: Limited by latency hiding capability

    queue_capacity = queue_depth * burst_len  # Total beats in flight
    fully_pipelined = queue_capacity >= latency

    if fully_pipelined:
        steady_state_bw = 1.0  # Ideal: 1 beat per cycle
    else:
        # Limited pipelining: Some stalls between bursts
        # Effective bandwidth reduces as latency hiding is incomplete
        steady_state_bw = queue_capacity / latency if latency > 0 else 1.0

    # Calculate total cycles for num_commands
    total_bursts = num_commands
    total_beats = total_bursts * burst_len

    # Startup cycles
    startup_cycles = startup_issue_cycles + startup_latency_cycles

    # Steady state cycles (after queue is primed)
    remaining_bursts = total_bursts - queue_depth
    remaining_beats = remaining_bursts * burst_len

    steady_state_cycles = remaining_beats / steady_state_bw if steady_state_bw > 0 else remaining_beats

    total_cycles = startup_cycles + steady_state_cycles
    overall_bandwidth = total_beats / total_cycles if total_cycles > 0 else 0

    debug_info = {
        'model': 'V2 (command pipelined)',
        'queue_depth': queue_depth,
        'fully_pipelined': fully_pipelined,
        'startup_cycles': startup_cycles,
        'steady_state_cycles': steady_state_cycles,
        'total_cycles': total_cycles,
        'total_beats': total_beats,
        'steady_state_bandwidth': steady_state_bw,
        'bandwidth_beats_per_cycle': overall_bandwidth,
        'efficiency_percent': overall_bandwidth * 100
    }

    return overall_bandwidth, debug_info


def v3_bandwidth_model(latency: int, burst_len: int, queue_depth: int,
                       num_commands: int = 1000, ooo_benefit: float = 1.04) -> Tuple[float, Dict]:
    """
    V3 bandwidth model - Out-of-order completion with deeper queues.

    V3 adds OOO capability to V2:
    - Read Engine: OOO R beat reception (transaction ID matching)
    - Write Engine: OOO W drain (select command with data available)

    Performance difference vs V2:
    - Best case: ~1.04x improvement (OOO hides memory reordering latency)
    - Typical: Marginal improvement (~1.02x) for in-order memory
    - Cost: 1.6-2.8x area increase vs V1

    Args:
        latency: Memory latency in cycles
        burst_len: Burst length in beats
        queue_depth: Command queue depth (typically larger than V2: 8-16)
        num_commands: Total commands to model
        ooo_benefit: OOO speedup factor vs V2 (1.0 = no benefit, 1.04 = 4% faster)

    Returns:
        (bandwidth_beats_per_cycle, debug_info)
    """
    # V3 baseline is V2 performance
    v2_bw, v2_info = v2_bandwidth_model(latency, burst_len, queue_depth, num_commands)

    # Apply OOO benefit
    v3_bw = min(v2_bw * ooo_benefit, 1.0)  # Can't exceed 1.0 beats/cycle

    # Recalculate cycles with improved bandwidth
    total_beats = num_commands * burst_len
    total_cycles = total_beats / v3_bw if v3_bw > 0 else total_beats

    debug_info = {
        'model': 'V3 (out-of-order)',
        'queue_depth': queue_depth,
        'ooo_benefit_factor': ooo_benefit,
        'v2_baseline_bandwidth': v2_bw,
        'v3_bandwidth': v3_bw,
        'total_cycles': total_cycles,
        'total_beats': total_beats,
        'bandwidth_beats_per_cycle': v3_bw,
        'efficiency_percent': v3_bw * 100,
        'speedup_vs_v2': v3_bw / v2_bw if v2_bw > 0 else 1.0
    }

    return v3_bw, debug_info


def predict_bandwidth_gbps(bandwidth_beats_per_cycle: float, data_width_bits: int,
                           clock_freq_mhz: int = 200) -> float:
    """
    Convert bandwidth (beats/cycle) to GB/s at given clock frequency.

    Args:
        bandwidth_beats_per_cycle: Bandwidth in beats per cycle
        data_width_bits: Data width in bits per beat
        clock_freq_mhz: Clock frequency in MHz (default 200 MHz)

    Returns:
        Bandwidth in GB/s
    """
    bytes_per_beat = data_width_bits / 8
    bytes_per_sec = bandwidth_beats_per_cycle * bytes_per_beat * clock_freq_mhz * 1e6
    gb_per_sec = bytes_per_sec / 1e9
    return gb_per_sec


def print_model_results(model_name: str, bandwidth: float, debug_info: Dict,
                       data_width_bits: int = 512, clock_freq_mhz: int = 200):
    """Print formatted model results."""
    gb_per_sec = predict_bandwidth_gbps(bandwidth, data_width_bits, clock_freq_mhz)

    print(f"\n{'='*80}")
    print(f"{model_name}")
    print(f"{'='*80}")
    print(f"Bandwidth: {bandwidth:.4f} beats/cycle ({bandwidth*100:.2f}% efficiency)")
    print(f"Bandwidth: {gb_per_sec:.2f} GB/s @ {clock_freq_mhz}MHz, {data_width_bits}-bit data")
    print(f"\nDebug Info:")
    for key, value in debug_info.items():
        if isinstance(value, float):
            print(f"  {key:.<40} {value:.4f}")
        else:
            print(f"  {key:.<40} {value}")


def main():
    """Main entry point for command-line usage."""
    parser = argparse.ArgumentParser(
        description='DMA Performance Model for V1/V2/V3 AXI Engines'
    )
    parser.add_argument('--version', choices=['v1', 'v2', 'v3', 'all'], default='all',
                       help='Which version to model')
    parser.add_argument('--latency', type=int, default=100,
                       help='Memory latency in cycles (default: 100 for DDR4)')
    parser.add_argument('--burst-len', type=int, default=16,
                       help='Burst length in beats (default: 16)')
    parser.add_argument('--queue-depth', type=int, default=8,
                       help='Command queue depth for V2/V3 (default: 8)')
    parser.add_argument('--data-width', type=int, default=512,
                       help='Data width in bits (default: 512)')
    parser.add_argument('--clock-freq', type=int, default=200,
                       help='Clock frequency in MHz (default: 200)')
    parser.add_argument('--num-commands', type=int, default=1000,
                       help='Number of commands to model (default: 1000)')

    args = parser.parse_args()

    print(f"DMA Performance Model")
    print(f"Parameters: latency={args.latency} cycles, burst_len={args.burst_len} beats")
    print(f"            queue_depth={args.queue_depth}, data_width={args.data_width} bits")
    print(f"            clock={args.clock_freq}MHz, commands={args.num_commands}")

    if args.version in ['v1', 'all']:
        bw, info = v1_bandwidth_model(args.latency, args.burst_len)
        print_model_results('V1 Model (Single Outstanding)', bw, info,
                          args.data_width, args.clock_freq)

    if args.version in ['v2', 'all']:
        bw, info = v2_bandwidth_model(args.latency, args.burst_len,
                                     args.queue_depth, args.num_commands)
        print_model_results('V2 Model (Command Pipelined)', bw, info,
                          args.data_width, args.clock_freq)

    if args.version in ['v3', 'all']:
        bw, info = v3_bandwidth_model(args.latency, args.burst_len,
                                     args.queue_depth, args.num_commands)
        print_model_results('V3 Model (Out-of-Order)', bw, info,
                          args.data_width, args.clock_freq)

    # Print comparison if modeling all versions
    if args.version == 'all':
        v1_bw, _ = v1_bandwidth_model(args.latency, args.burst_len)
        v2_bw, _ = v2_bandwidth_model(args.latency, args.burst_len,
                                     args.queue_depth, args.num_commands)
        v3_bw, _ = v3_bandwidth_model(args.latency, args.burst_len,
                                     args.queue_depth, args.num_commands)

        print(f"\n{'='*80}")
        print(f"Comparison Summary")
        print(f"{'='*80}")
        print(f"V1 Bandwidth: {v1_bw:.4f} beats/cycle ({v1_bw*100:.2f}%)")
        print(f"V2 Bandwidth: {v2_bw:.4f} beats/cycle ({v2_bw*100:.2f}%) → "
              f"{v2_bw/v1_bw:.2f}x speedup vs V1")
        print(f"V3 Bandwidth: {v3_bw:.4f} beats/cycle ({v3_bw*100:.2f}%) → "
              f"{v3_bw/v1_bw:.2f}x speedup vs V1")


if __name__ == '__main__':
    main()
