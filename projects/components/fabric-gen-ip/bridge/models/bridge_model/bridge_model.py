#!/usr/bin/env python3
"""
Bridge Performance Model for AXI4 Crossbar Variants

Purpose: Analytical model to predict latency and throughput based on:
         - Topology (M masters × N slaves)
         - Arbitration scheme (round-robin, priority)
         - ID tracking method (flat pass-through, distributed RAM, CAM)
         - Traffic patterns (uniform, hotspot, bursty)

Author: RTL Design Sherpa
Created: 2025-10-28
"""

import argparse
from typing import Dict, List, Tuple
from enum import Enum


# ===========================================================================
# Bridge Architecture Variants
# ===========================================================================

class BridgeVariant(Enum):
    """Bridge implementation variants from simplest to most complex."""
    V1_FLAT = "v1_flat"           # Basic flat crossbar, simple ID pass-through
    V2_DISTRAM = "v2_distram"     # Distributed RAM ID tables for OOO
    V3_CAM = "v3_cam"             # CAM-based transaction tracking
    V4_PIPELINE = "v4_pipeline"   # Pipelined with FIFO stages


class ArbitrationScheme(Enum):
    """Arbitration schemes for resolving master conflicts."""
    ROUND_ROBIN = "round_robin"   # Fair, no starvation
    PRIORITY = "priority"         # Low latency for high-pri masters
    WEIGHTED_RR = "weighted_rr"   # Balanced fairness + priority


# ===========================================================================
# V1 Flat Crossbar Model - Basic, Lowest Performance
# ===========================================================================

def v1_flat_latency_model(
    num_masters: int,
    num_slaves: int,
    arbitration: ArbitrationScheme = ArbitrationScheme.ROUND_ROBIN
) -> Tuple[int, int, int, Dict]:
    """
    V1 Flat Crossbar - Simplest implementation.

    Architecture:
    - Basic M×N multiplexer array
    - Simple round-robin or priority arbitration
    - ID pass-through (no tracking tables)
    - No pipelining (combinational address decode + registered output)

    Latency Components:
    1. Address decode: 1 cycle (combinational → registered)
    2. Arbitration: 0-1 cycles (0 if no conflict, 1 if contested)
    3. Data multiplexing: 0 cycles (combinational)
    4. Output register: 1 cycle

    Args:
        num_masters: Number of master interfaces (M)
        num_slaves: Number of slave interfaces (N)
        arbitration: Arbitration scheme (affects contention delay)

    Returns:
        (min_latency, typical_latency, max_latency, debug_info)
    """

    # Component latencies (cycles)
    decode_latency = 1      # Address decode (combinational → flop)
    output_reg = 1          # Output register for timing closure

    # Arbitration latency depends on contention
    # Min: No conflict (grant immediate)
    # Max: Worst-case conflict (all M masters want same slave)
    if arbitration == ArbitrationScheme.ROUND_ROBIN:
        arb_min = 0         # No conflict
        arb_typical = 0     # Assuming low contention
        arb_max = num_masters - 1  # Worst case: wait for all others
    elif arbitration == ArbitrationScheme.PRIORITY:
        arb_min = 0         # High-priority master
        arb_typical = 0     # Assuming most are high-priority
        arb_max = 1         # Low-priority waits 1 cycle
    else:  # WEIGHTED_RR
        arb_min = 0
        arb_typical = 0
        arb_max = (num_masters - 1) // 2  # Better than RR for low-pri

    min_latency = decode_latency + arb_min + output_reg
    typical_latency = decode_latency + arb_typical + output_reg
    max_latency = decode_latency + arb_max + output_reg

    debug_info = {
        'variant': 'V1 Flat Crossbar (Basic)',
        'topology': f'{num_masters}×{num_slaves}',
        'arbitration': arbitration.value,
        'decode_cycles': decode_latency,
        'arb_min_cycles': arb_min,
        'arb_typical_cycles': arb_typical,
        'arb_max_cycles': arb_max,
        'output_reg_cycles': output_reg,
        'min_latency_cycles': min_latency,
        'typical_latency_cycles': typical_latency,
        'max_latency_cycles': max_latency,
        'notes': [
            'Min latency: No contention (uncontested slave access)',
            'Typical: Low contention (≤20% of requests conflict)',
            'Max latency: Heavy contention (all masters → same slave)'
        ]
    }

    return min_latency, typical_latency, max_latency, debug_info


def v1_flat_throughput_model(
    num_masters: int,
    num_slaves: int,
    traffic_pattern: str = 'uniform'
) -> Tuple[int, float, Dict]:
    """
    V1 Flat Crossbar - Throughput analysis.

    Key Insight: A flat M×N crossbar can support up to min(M, N) concurrent
    non-conflicting transfers in the best case.

    Throughput Analysis:
    - Best case: min(M, N) concurrent transfers (all to different slaves)
    - Worst case: 1 transfer (all masters → same slave)
    - Typical: Depends on traffic pattern

    Traffic Patterns:
    - 'uniform': Each master evenly distributes across all slaves
    - 'hotspot': One popular slave gets 80% of traffic
    - 'dedicated': Each master has primary slave (90% traffic)

    Args:
        num_masters: Number of master interfaces
        num_slaves: Number of slave interfaces
        traffic_pattern: Traffic distribution pattern

    Returns:
        (max_concurrent, avg_throughput_ratio, debug_info)
    """

    # Maximum possible concurrent transfers
    max_concurrent = min(num_masters, num_slaves)

    # Average throughput depends on traffic pattern
    if traffic_pattern == 'uniform':
        # Uniform traffic: Low contention
        # Probability that 2 masters target same slave: 1/N
        # Expected concurrent transfers ≈ M * (1 - 1/N) for M ≤ N
        if num_masters <= num_slaves:
            # Each master likely gets a slave
            avg_concurrent = num_masters * (1 - 1/num_slaves)
        else:
            # More masters than slaves, limited by slaves
            avg_concurrent = num_slaves * 0.8  # ~80% utilization
        avg_throughput_ratio = avg_concurrent / max_concurrent

    elif traffic_pattern == 'hotspot':
        # One slave gets 80% of traffic → heavy contention
        # Hotspot slave: serialized (1 transfer at a time)
        # Other slaves: shared by remaining 20% traffic
        hotspot_throughput = 1.0  # Serialized
        other_throughput = (num_slaves - 1) * 0.2  # Low utilization
        avg_concurrent = hotspot_throughput + other_throughput
        avg_throughput_ratio = avg_concurrent / max_concurrent

    elif traffic_pattern == 'dedicated':
        # Each master primarily accesses one slave (90% affinity)
        # Very low contention
        if num_masters <= num_slaves:
            avg_concurrent = num_masters * 0.95  # 95% parallel efficiency
        else:
            avg_concurrent = num_slaves * 0.9   # 90% slave utilization
        avg_throughput_ratio = avg_concurrent / max_concurrent

    else:
        # Unknown pattern, assume moderate contention
        avg_concurrent = max_concurrent * 0.6
        avg_throughput_ratio = 0.6

    debug_info = {
        'variant': 'V1 Flat Crossbar (Basic)',
        'topology': f'{num_masters}×{num_slaves}',
        'traffic_pattern': traffic_pattern,
        'max_concurrent_transfers': max_concurrent,
        'avg_concurrent_transfers': f'{avg_concurrent:.2f}',
        'avg_throughput_ratio': f'{avg_throughput_ratio:.2%}',
        'bottleneck': 'Slave contention' if traffic_pattern == 'hotspot' else 'Minimal',
        'notes': [
            f'Best case: {max_concurrent} concurrent transfers (all to different slaves)',
            'Worst case: 1 transfer (all masters → same slave)',
            f'Traffic pattern: {traffic_pattern}'
        ]
    }

    return max_concurrent, avg_throughput_ratio, debug_info


# ===========================================================================
# V2/V3/V4 Placeholder Models (Future Implementation)
# ===========================================================================

def v2_distram_model(*args, **kwargs):
    """V2 with distributed RAM ID tables - Future implementation."""
    raise NotImplementedError("V2 model not yet implemented. Use V1 for now.")


def v3_cam_model(*args, **kwargs):
    """V3 with CAM-based transaction tracking - Future implementation."""
    raise NotImplementedError("V3 model not yet implemented. Use V1 for now.")


def v4_pipeline_model(*args, **kwargs):
    """V4 with FIFO pipeline stages - Future implementation."""
    raise NotImplementedError("V4 model not yet implemented. Use V1 for now.")


# ===========================================================================
# Utility Functions
# ===========================================================================

def predict_bandwidth_gbps(
    throughput_ratio: float,
    data_width_bits: int,
    clock_freq_mhz: int = 200
) -> float:
    """
    Convert throughput ratio to GB/s at given clock frequency.

    Args:
        throughput_ratio: Ratio of achieved to max throughput (0.0-1.0)
        data_width_bits: Data width in bits per beat
        clock_freq_mhz: Clock frequency in MHz

    Returns:
        Bandwidth in GB/s
    """
    bytes_per_beat = data_width_bits / 8
    max_bytes_per_sec = bytes_per_beat * clock_freq_mhz * 1e6
    actual_bytes_per_sec = max_bytes_per_sec * throughput_ratio
    gb_per_sec = actual_bytes_per_sec / 1e9
    return gb_per_sec


def print_latency_results(
    min_lat: int, typ_lat: int, max_lat: int,
    debug_info: Dict, clock_freq_mhz: int = 200
):
    """Print formatted latency model results."""
    ns_per_cycle = 1000 / clock_freq_mhz

    print(f"\n{'='*80}")
    print(f"Bridge Latency Model: {debug_info['variant']}")
    print(f"{'='*80}")
    print(f"Topology: {debug_info['topology']}")
    print(f"Arbitration: {debug_info['arbitration']}")
    print(f"\nLatency (cycles):")
    print(f"  Minimum:  {min_lat} cycles ({min_lat * ns_per_cycle:.1f} ns @ {clock_freq_mhz}MHz)")
    print(f"  Typical:  {typ_lat} cycles ({typ_lat * ns_per_cycle:.1f} ns @ {clock_freq_mhz}MHz)")
    print(f"  Maximum:  {max_lat} cycles ({max_lat * ns_per_cycle:.1f} ns @ {clock_freq_mhz}MHz)")

    print(f"\nComponent Breakdown:")
    print(f"  Address decode:   {debug_info['decode_cycles']} cycle")
    print(f"  Arbitration:      {debug_info['arb_min_cycles']}-{debug_info['arb_max_cycles']} cycles")
    print(f"  Output register:  {debug_info['output_reg_cycles']} cycle")

    if 'notes' in debug_info:
        print(f"\nNotes:")
        for note in debug_info['notes']:
            print(f"  - {note}")


def print_throughput_results(
    max_concurrent: int, avg_ratio: float,
    debug_info: Dict, data_width_bits: int = 512, clock_freq_mhz: int = 200
):
    """Print formatted throughput model results."""
    gb_per_sec = predict_bandwidth_gbps(avg_ratio, data_width_bits, clock_freq_mhz)

    print(f"\n{'='*80}")
    print(f"Bridge Throughput Model: {debug_info['variant']}")
    print(f"{'='*80}")
    print(f"Topology: {debug_info['topology']}")
    print(f"Traffic Pattern: {debug_info['traffic_pattern']}")
    print(f"\nThroughput:")
    print(f"  Max concurrent transfers: {max_concurrent}")
    print(f"  Avg concurrent transfers: {debug_info['avg_concurrent_transfers']}")
    print(f"  Avg throughput ratio:     {debug_info['avg_throughput_ratio']}")
    print(f"  Estimated bandwidth:      {gb_per_sec:.2f} GB/s @ {clock_freq_mhz}MHz, {data_width_bits}-bit data")
    print(f"\nBottleneck: {debug_info['bottleneck']}")

    if 'notes' in debug_info:
        print(f"\nNotes:")
        for note in debug_info['notes']:
            print(f"  - {note}")


# ===========================================================================
# Main Entry Point
# ===========================================================================

def main():
    """Main entry point for command-line usage."""
    parser = argparse.ArgumentParser(
        description='Bridge Performance Model for AXI4 Crossbar Variants',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Basic 4×4 crossbar latency
  ./bridge_model.py --variant v1_flat --masters 4 --slaves 4 --latency

  # Throughput analysis with uniform traffic
  ./bridge_model.py --variant v1_flat --masters 8 --slaves 4 --throughput --traffic uniform

  # Hotspot scenario (80% traffic to one slave)
  ./bridge_model.py --variant v1_flat --masters 4 --slaves 4 --throughput --traffic hotspot

  # Combined analysis
  ./bridge_model.py --variant v1_flat --masters 4 --slaves 4 --latency --throughput
        """
    )

    parser.add_argument('--variant', choices=['v1_flat', 'v2_distram', 'v3_cam', 'v4_pipeline'],
                       default='v1_flat', help='Bridge variant to model (default: v1_flat)')
    parser.add_argument('--masters', type=int, default=4,
                       help='Number of master interfaces (default: 4)')
    parser.add_argument('--slaves', type=int, default=4,
                       help='Number of slave interfaces (default: 4)')
    parser.add_argument('--arbitration', choices=['round_robin', 'priority', 'weighted_rr'],
                       default='round_robin', help='Arbitration scheme (default: round_robin)')
    parser.add_argument('--latency', action='store_true',
                       help='Show latency analysis')
    parser.add_argument('--throughput', action='store_true',
                       help='Show throughput analysis')
    parser.add_argument('--traffic', choices=['uniform', 'hotspot', 'dedicated'],
                       default='uniform', help='Traffic pattern (default: uniform)')
    parser.add_argument('--data-width', type=int, default=512,
                       help='Data width in bits (default: 512)')
    parser.add_argument('--clock-freq', type=int, default=200,
                       help='Clock frequency in MHz (default: 200)')

    args = parser.parse_args()

    # Default to showing both if neither specified
    if not args.latency and not args.throughput:
        args.latency = True
        args.throughput = True

    print(f"Bridge Performance Model")
    print(f"Variant: {args.variant}")
    print(f"Configuration: {args.masters} masters × {args.slaves} slaves")
    print(f"Clock: {args.clock_freq}MHz, Data Width: {args.data_width} bits")

    # Dispatch to appropriate variant
    if args.variant == 'v1_flat':
        arb_scheme = ArbitrationScheme[args.arbitration.upper()]

        if args.latency:
            min_lat, typ_lat, max_lat, debug = v1_flat_latency_model(
                args.masters, args.slaves, arb_scheme
            )
            print_latency_results(min_lat, typ_lat, max_lat, debug, args.clock_freq)

        if args.throughput:
            max_conc, avg_ratio, debug = v1_flat_throughput_model(
                args.masters, args.slaves, args.traffic
            )
            print_throughput_results(max_conc, avg_ratio, debug,
                                    args.data_width, args.clock_freq)

    else:
        # V2/V3/V4 not yet implemented
        if args.variant == 'v2_distram':
            v2_distram_model()
        elif args.variant == 'v3_cam':
            v3_cam_model()
        elif args.variant == 'v4_pipeline':
            v4_pipeline_model()


if __name__ == '__main__':
    main()
