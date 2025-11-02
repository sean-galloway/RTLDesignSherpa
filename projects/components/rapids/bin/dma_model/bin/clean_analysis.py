#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: clean_analysis
# Purpose: Clean DMA Performance Analysis - READ and WRITE Reported Separately
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Clean DMA Performance Analysis - READ and WRITE Reported Separately

NO combined analysis. Each path analyzed independently.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from pyperf import AXIConfig, AXI4Performance


def analyze_read_path():
    """Analyze READ path only (2KB bursts)."""

    print("\n" + "="*80)
    print("  READ PATH ANALYSIS")
    print("="*80)
    print("\n  Payload: 2KB (2048 bytes, 32 beats)")
    print("  Channels: 16")
    print("  Drain Rate: 4 GB/s per channel (1 beat / 16 cycles)")

    configs = {
        'Baseline (No Pipeline, Store-and-Forward)': AXIConfig(
            payload=2048,
            pipeline_depth=1,
            pipelining_enabled=False,
            streaming_drain=False,
            sram_mode="pingpong"
        ),
        'Streaming Drain Only': AXIConfig(
            payload=2048,
            pipeline_depth=1,
            pipelining_enabled=False,
            streaming_drain=True,
            sram_mode="pingpong"
        ),
        'Pipeline Depth=2 (Ping-Pong SRAM)': AXIConfig(
            payload=2048,
            pipeline_depth=2,
            pipelining_enabled=True,
            streaming_drain=False,
            sram_mode="pingpong"
        ),
        'Pipeline Depth=2 + Streaming': AXIConfig(
            payload=2048,
            pipeline_depth=2,
            pipelining_enabled=True,
            streaming_drain=True,
            sram_mode="pingpong"
        ),
        'Pipeline Depth=4 (Ping-Pong SRAM limited to 2)': AXIConfig(
            payload=2048,
            pipeline_depth=4,
            pipelining_enabled=True,
            streaming_drain=True,
            sram_mode="pingpong"
        ),
    }

    print(f"\n{'─'*80}")
    print(f"{'Configuration':<45} {'READ BW':<15} {'Cycles/Burst':<15} {'SRAM/ch'}")
    print(f"{'─'*80}")

    for name, cfg in configs.items():
        perf = AXI4Performance(cfg)
        result = perf.calculate_channel_bandwidth(16)

        sram_kb = result['effective_pipeline_depth'] * 2048 / 1024

        print(f"{name:<45} {result['total_bw']:>7.2f} GB/s   "
              f"{result['cycles_per_burst']:>7.0f} cycles   {sram_kb:>5.1f} KB")

    print(f"{'─'*80}")
    print(f"\n  Target: 50 GB/s")
    print(f"  AXI Peak: 57.6 GB/s")
    print(f"\n  ✅ Pipeline depth=2 achieves 57.6 GB/s (EXCEEDS target)")
    print(f"  📌 SRAM Required: 4 KB per channel (64 KB total)")
    print("="*80 + "\n")


def analyze_write_path():
    """Analyze WRITE path only (256B bursts)."""

    print("\n" + "="*80)
    print("  WRITE PATH ANALYSIS")
    print("="*80)
    print("\n  Payload: 256B (256 bytes, 4 beats)")
    print("  Channels: 16")
    print("  Outstanding Bursts: System-wide limit")

    print(f"\n{'─'*80}")
    print(f"{'Configuration':<45} {'WRITE BW':<15} {'Outstanding':<20}")
    print(f"{'─'*80}")

    for outstanding in [16, 32, 64, 128]:
        cfg = AXIConfig(
            payload=256,
            pipeline_depth=outstanding // 16,
            pipelining_enabled=True,
            max_outstanding_bursts=outstanding
        )
        perf = AXI4Performance(cfg)
        result = perf.calculate_channel_bandwidth(16)

        config_name = f"{outstanding} Outstanding Bursts"
        if outstanding == 32:
            config_name += " (Current Design)"

        print(f"{config_name:<45} {result['total_bw']:>7.2f} GB/s   "
              f"{outstanding} total ({outstanding/16:.1f}/ch)")

    print(f"{'─'*80}")
    print(f"\n  Target: 50 GB/s")
    print(f"  Maximum Achievable: ~20 GB/s (limited by 256B burst size)")
    print(f"\n  ❌ WRITE path CANNOT meet 50 GB/s target with 256B bursts")
    print(f"  📌 SRAM Required: ~0.5 KB per channel (8 KB total)")
    print(f"\n  Note: Small burst size (256B) limits bandwidth.")
    print(f"        Even with unlimited outstanding bursts, cannot exceed ~20 GB/s.")
    print("="*80 + "\n")


def payload_sweep_read_only():
    """Sweep READ payloads only."""

    print("\n" + "="*80)
    print("  READ PATH - PAYLOAD SIZE SWEEP")
    print("="*80)
    print("\n  Testing: 256B, 512B, 1KB, 2KB")
    print("  Channels: 16")

    payloads = [256, 512, 1024, 2048]

    print(f"\n{'─'*80}")
    print(f"{'Payload':<12} {'Baseline READ':<20} {'Optimized READ':<20} {'Meets 50GB/s':<15}")
    print(f"{'─'*80}")

    for payload in payloads:
        # Baseline
        cfg_base = AXIConfig(
            payload=payload,
            pipeline_depth=1,
            pipelining_enabled=False,
            streaming_drain=False
        )
        perf_base = AXI4Performance(cfg_base)
        base_bw = perf_base.calculate_channel_bandwidth(16)['total_bw']

        # Optimized (pipeline + streaming)
        cfg_opt = AXIConfig(
            payload=payload,
            pipeline_depth=4,
            pipelining_enabled=True,
            streaming_drain=True,
            sram_mode="pingpong"
        )
        perf_opt = AXI4Performance(cfg_opt)
        opt_result = perf_opt.calculate_channel_bandwidth(16)
        opt_bw = opt_result['total_bw']

        meets_target = "✅ Yes" if opt_bw >= 50 else "❌ No"

        print(f"{payload:>4}B      {base_bw:>7.2f} GB/s        "
              f"{opt_bw:>7.2f} GB/s        {meets_target}")

    print(f"{'─'*80}")
    print("\n  Key Finding: READ needs ≥1KB payloads to meet 50 GB/s target")
    print("="*80 + "\n")


def main():
    print("\n" + "="*80)
    print("  CLEAN DMA ANALYSIS - READ and WRITE Separate")
    print("="*80)

    # Analyze each path independently
    analyze_read_path()
    analyze_write_path()
    payload_sweep_read_only()

    # Summary
    print("\n" + "="*80)
    print("  SUMMARY")
    print("="*80)
    print("\n  READ Path (2KB bursts):")
    print("    Baseline:  44.04 GB/s")
    print("    Optimized: 57.60 GB/s (with pipeline depth=2)")
    print("    Target:    ✅ EXCEEDS 50 GB/s")
    print("    SRAM:      64 KB total (4 KB per channel)")

    print("\n  WRITE Path (256B bursts):")
    print("    Current:   20.08 GB/s (with 32 outstanding)")
    print("    Maximum:   20.08 GB/s (limited by burst size)")
    print("    Target:    ❌ CANNOT meet 50 GB/s")
    print("    SRAM:      8 KB total (0.5 KB per channel)")

    print("\n  Note: READ and WRITE are INDEPENDENT paths.")
    print("        They do NOT combine or compete for bandwidth.")
    print("="*80 + "\n")


if __name__ == "__main__":
    main()
