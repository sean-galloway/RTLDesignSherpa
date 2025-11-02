# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PerformanceReporter
# Purpose: STREAM DMA Performance Reporting Module
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-18

"""
STREAM DMA Performance Reporting Module

Generates detailed analysis reports covering:
- Bottleneck analysis
- Design limitations
- Optimization recommendations
- Latency sensitivity
- SRAM sizing analysis
"""

import pandas as pd
from typing import Dict, List, Optional
from .performance import (
    AXIConfig, StreamDMAConfig, StreamDMAPerformance, PerformanceMode,
    create_mode_configs, DEFAULT_W, DEFAULT_F, DEFAULT_ALPHA,
    DEFAULT_LATENCY, MAX_CHANNELS
)


class PerformanceReporter:
    """Generate comprehensive performance analysis reports"""

    def __init__(self, output_dir: str = "reports"):
        self.output_dir = output_dir

    def generate_bottleneck_report(self, mode: PerformanceMode, payload: int = 1024) -> str:
        """
        Generate detailed bottleneck analysis report.

        Args:
            mode: Performance mode to analyze
            payload: Burst size in bytes

        Returns:
            Markdown-formatted report string
        """
        config = create_mode_configs(mode, payload)
        dma_perf = StreamDMAPerformance(config)

        report = []
        report.append(f"# STREAM DMA Bottleneck Analysis: {mode.value} Mode\n")
        report.append(f"**Payload:** {payload} bytes ({payload // 64} beats @ 512-bit bus)\n")
        report.append(f"**Generated:** STREAM DMA Performance Model v1.0\n")
        report.append("\n---\n")

        # Configuration summary
        report.append("## Configuration Summary\n")
        report.append(f"| Parameter | Read Engine | Write Engine |")
        report.append(f"|-----------|-------------|--------------|")
        report.append(f"| Max Burst Length | {config.read_config.max_burst_len} beats | {config.write_config.max_burst_len} beats |")
        report.append(f"| Max Outstanding | {config.read_config.max_outstanding} | {config.write_config.max_outstanding} |")
        report.append(f"| Pipeline Depth | {config.read_config.pipeline_depth} | {config.write_config.pipeline_depth} |")
        report.append(f"| SRAM per Channel | {config.read_config.sram_lines_per_channel} lines ({config.read_config.sram_per_channel // 1024} KB) | {config.write_config.sram_lines_per_channel} lines ({config.write_config.sram_per_channel // 1024} KB) |")
        report.append("")

        # Single channel analysis
        report.append("## Single Channel Analysis\n")

        read_1ch = dma_perf.read_perf.calculate_channel_bandwidth(1)
        write_1ch = dma_perf.write_perf.calculate_channel_bandwidth(1)

        report.append("### Read Path")
        report.append(f"- **Effective Pipeline:** {read_1ch['effective_pipeline']} (limited by {self._explain_pipeline_limit(read_1ch, config.read_config)})")
        report.append(f"- **Cycles per Burst:** {read_1ch['cycles_per_burst']:.1f} cycles")
        report.append(f"- **Bandwidth:** {read_1ch['B_channel']:.2f} GB/s ({read_1ch['efficiency']:.1f}% of AXI peak)")
        report.append(f"- **Bottleneck:** {self._explain_bottleneck(read_1ch)}\n")

        report.append("### Write Path")
        report.append(f"- **Effective Pipeline:** {write_1ch['effective_pipeline']} (limited by {self._explain_pipeline_limit(write_1ch, config.write_config)})")
        report.append(f"- **Cycles per Burst:** {write_1ch['cycles_per_burst']:.1f} cycles")
        report.append(f"- **Bandwidth:** {write_1ch['B_channel']:.2f} GB/s ({write_1ch['efficiency']:.1f}% of AXI peak)")
        report.append(f"- **Bottleneck:** {self._explain_bottleneck(write_1ch)}\n")

        # Multi-channel scaling
        report.append("## Multi-Channel Scaling Analysis\n")

        scaling_data = []
        for num_ch in [1, 2, 4, 8]:
            dma_result = dma_perf.calculate_dma_bandwidth(num_ch)
            scaling_data.append({
                'Channels': num_ch,
                'Read_BW': dma_result['read_bw'],
                'Write_BW': dma_result['write_bw'],
                'DMA_Throughput': dma_result['dma_throughput'],
                'Read_Eff': dma_result['read_efficiency'],
                'Write_Eff': dma_result['write_efficiency'],
                'Bottleneck': dma_result['bottleneck']
            })

        df = pd.DataFrame(scaling_data)
        report.append(df.to_markdown(index=False))
        report.append("")

        # Bottleneck explanation
        report.append("## Bottleneck Explanation\n")

        dma_8ch = dma_perf.calculate_dma_bandwidth(8)

        if dma_8ch['bottleneck'] == 'read_path':
            report.append("**Primary Bottleneck: Read Path**\n")
            report.append(f"- Read bandwidth ({dma_8ch['read_bw']:.2f} GB/s) < Write bandwidth ({dma_8ch['write_bw']:.2f} GB/s)")
            report.append(f"- Overall DMA throughput limited to {dma_8ch['read_bw']:.2f} GB/s by read engine")
            report.append(f"- Read path limited by: {dma_8ch['read_limited_by']}\n")

        elif dma_8ch['bottleneck'] == 'write_path':
            report.append("**Primary Bottleneck: Write Path**\n")
            report.append(f"- Write bandwidth ({dma_8ch['write_bw']:.2f} GB/s) < Read bandwidth ({dma_8ch['read_bw']:.2f} GB/s)")
            report.append(f"- Overall DMA throughput limited to {dma_8ch['write_bw']:.2f} GB/s by write engine")
            report.append(f"- Write path limited by: {dma_8ch['write_limited_by']}\n")

        else:  # balanced
            report.append("**Balanced Performance**\n")
            report.append(f"- Read and write bandwidth equal: {dma_8ch['read_bw']:.2f} GB/s")
            report.append(f"- No single-path bottleneck - optimal balance achieved")
            if dma_8ch['read_efficiency'] >= 99.9:
                report.append(f"- AXI bus saturated at {dma_8ch['read_bw']:.2f} GB/s\n")
            else:
                report.append(f"- Both paths limited by: {dma_8ch['read_limited_by']}\n")

        # Design limitations
        report.append("## Design Limitations\n")

        limitations = self._identify_limitations(config, read_1ch, write_1ch)
        for limitation in limitations:
            report.append(f"- {limitation}")
        report.append("")

        # Optimization recommendations
        report.append("## Optimization Recommendations\n")

        recommendations = self._generate_recommendations(mode, config, read_1ch, write_1ch, dma_8ch)
        for rec in recommendations:
            report.append(f"- {rec}")
        report.append("")

        return "\n".join(report)

    def generate_latency_sensitivity_report(self, mode: PerformanceMode, payload: int = 1024) -> str:
        """
        Analyze sensitivity to memory latency.

        Args:
            mode: Performance mode to analyze
            payload: Burst size in bytes

        Returns:
            Markdown-formatted report string
        """
        report = []
        report.append(f"# Memory Latency Sensitivity Analysis: {mode.value} Mode\n")
        report.append(f"**Payload:** {payload} bytes\n")
        report.append("\n---\n")

        report.append("## Single Channel Performance vs Latency\n")

        latencies = [50, 100, 200, 400, 800]
        latency_data = []

        for latency in latencies:
            # Create custom config with specific latency
            config = create_mode_configs(mode, payload)
            config.read_config.latency = latency
            config.write_config.latency = latency

            # Recalculate derived parameters
            config.read_config.__post_init__()
            config.write_config.__post_init__()

            dma_perf = StreamDMAPerformance(config)
            read_1ch = dma_perf.read_perf.calculate_channel_bandwidth(1)
            write_1ch = dma_perf.write_perf.calculate_channel_bandwidth(1)

            latency_data.append({
                'Latency_Cycles': latency,
                'Read_BW_GBps': read_1ch['B_channel'],
                'Write_BW_GBps': write_1ch['B_channel'],
                'Read_Cycles_per_Burst': read_1ch['cycles_per_burst'],
                'Write_Cycles_per_Burst': write_1ch['cycles_per_burst'],
                'Read_Limited_By': read_1ch['limited_by'],
                'Write_Limited_By': write_1ch['limited_by']
            })

        df = pd.DataFrame(latency_data)
        report.append(df.to_markdown(index=False))
        report.append("")

        report.append("## Key Insights\n")
        report.append(f"- **{mode.value} mode** pipelining effectiveness vs latency:")

        if mode == PerformanceMode.LOW:
            report.append("  - No pipelining: Performance degrades linearly with latency")
            report.append("  - Bandwidth ∝ 1/(latency + burst_length)")
        elif mode == PerformanceMode.MEDIUM:
            report.append("  - 4-deep pipeline: Partially hides latency")
            report.append("  - Effective latency reduced by 4x at low latencies")
        elif mode == PerformanceMode.HIGH:
            report.append("  - Deep pipeline: Significantly hides latency")
            report.append("  - SRAM capacity may limit effectiveness at high latencies")
        elif mode == PerformanceMode.PERFECT:
            report.append("  - Unlimited pipeline: Completely hides latency up to SRAM capacity")
            report.append("  - Performance remains constant until SRAM saturation")

        report.append("")

        return "\n".join(report)

    def generate_sram_sizing_report(self, payload: int = 1024) -> str:
        """
        Analyze SRAM sizing requirements across modes.

        Args:
            payload: Burst size in bytes

        Returns:
            Markdown-formatted report string
        """
        report = []
        report.append("# SRAM Sizing Analysis\n")
        report.append(f"**Payload:** {payload} bytes ({payload // 64} beats)\n")
        report.append("\n---\n")

        report.append("## SRAM Requirements by Performance Mode\n")

        sram_data = []
        for mode in [PerformanceMode.LOW, PerformanceMode.MEDIUM, PerformanceMode.HIGH, PerformanceMode.PERFECT]:
            config = create_mode_configs(mode, payload)

            # Calculate bursts that fit in SRAM
            bursts_fit = config.read_config.sram_capacity_bursts

            # Calculate what would saturate with single channel
            peak_bw = config.read_config.Bmax
            cycles_to_saturate = payload * config.read_config.f / peak_bw
            pipeline_to_saturate = config.read_config.latency / (cycles_to_saturate - config.read_config.effective_BL)
            sram_to_saturate = max(1, int(pipeline_to_saturate * config.read_config.effective_BL))

            sram_data.append({
                'Mode': mode.value,
                'Pipeline_Depth': config.read_config.pipeline_depth,
                'SRAM_Lines': config.read_config.sram_lines_per_channel,
                'SRAM_KB': config.read_config.sram_per_channel // 1024,
                'Bursts_Fit': bursts_fit,
                'Eff_Pipeline': config.read_config.effective_pipeline,
                'Lines_to_Saturate_1ch': sram_to_saturate,
                'Saturates_8ch': 'Yes' if mode in [PerformanceMode.MEDIUM, PerformanceMode.HIGH, PerformanceMode.PERFECT] else 'No'
            })

        df = pd.DataFrame(sram_data)
        report.append(df.to_markdown(index=False))
        report.append("")

        report.append("## Design Tradeoffs\n")
        report.append("### Current Design (LOW/MEDIUM/HIGH modes)")
        report.append("- **SRAM per channel:** 128 lines (8 KB)")
        report.append("- **Total SRAM (8 channels):** 1024 lines (64 KB)")
        report.append("- **Strategy:** Channel parallelism over deep per-channel buffers\n")

        report.append("### PERFECT Mode (Theoretical Maximum)")
        perfect_config = create_mode_configs(PerformanceMode.PERFECT, payload)
        report.append(f"- **SRAM per channel:** {perfect_config.read_config.sram_lines_per_channel} lines ({perfect_config.read_config.sram_per_channel // 1024} KB)")
        report.append(f"- **Total SRAM (8 channels):** {perfect_config.read_config.sram_lines_per_channel * 8} lines ({perfect_config.read_config.sram_per_channel * 8 // 1024} KB)")
        report.append(f"- **Increase:** {perfect_config.read_config.sram_lines_per_channel // 128}x more SRAM per channel")
        report.append(f"- **Benefit:** Single channel can saturate bus\n")

        report.append("### Why Not Use PERFECT Mode?")
        report.append("1. **Area Cost:** 16x more SRAM (64 KB → 1024 KB total)")
        report.append("2. **Diminishing Returns:** No throughput gain when using multiple channels")
        report.append("3. **Real-World Usage:** Applications naturally partition across channels")
        report.append("4. **Flexibility:** Multiple channels support concurrent independent operations\n")

        return "\n".join(report)

    def generate_complete_report(self, mode: PerformanceMode, payload: int = 1024,
                                 output_file: Optional[str] = None) -> str:
        """
        Generate complete analysis report combining all sections.

        Args:
            mode: Performance mode to analyze
            payload: Burst size in bytes
            output_file: Optional file path to save report

        Returns:
            Complete markdown-formatted report
        """
        report = []

        # Title
        report.append(f"# STREAM DMA Complete Performance Report")
        report.append(f"## {mode.value} Performance Mode Analysis\n")
        report.append(f"**Payload:** {payload} bytes\n")
        report.append(f"**AXI Interface:** 512-bit @ 1.0 GHz (Peak: 57.6 GB/s)")
        report.append(f"**Memory Latency:** {DEFAULT_LATENCY} cycles\n")
        report.append("\n" + "="*80 + "\n")

        # Section 1: Bottleneck Analysis
        report.append(self.generate_bottleneck_report(mode, payload))
        report.append("\n" + "="*80 + "\n")

        # Section 2: Latency Sensitivity
        report.append(self.generate_latency_sensitivity_report(mode, payload))
        report.append("\n" + "="*80 + "\n")

        # Section 3: SRAM Sizing (only for complete report)
        if mode == PerformanceMode.HIGH or mode == PerformanceMode.PERFECT:
            report.append(self.generate_sram_sizing_report(payload))
            report.append("\n" + "="*80 + "\n")

        # Final summary
        report.append("# Summary and Recommendations\n")

        config = create_mode_configs(mode, payload)
        dma_perf = StreamDMAPerformance(config)
        dma_8ch = dma_perf.calculate_dma_bandwidth(8)

        report.append(f"## {mode.value} Mode Performance")
        report.append(f"- **Single Channel:** {dma_perf.read_perf.calculate_channel_bandwidth(1)['B_channel']:.2f} GB/s (read), {dma_perf.write_perf.calculate_channel_bandwidth(1)['B_channel']:.2f} GB/s (write)")
        report.append(f"- **8 Channels:** {dma_8ch['dma_throughput']:.2f} GB/s DMA throughput")
        report.append(f"- **Efficiency:** {dma_8ch['read_efficiency']:.1f}% of AXI peak")
        report.append(f"- **Bottleneck:** {dma_8ch['bottleneck']}\n")

        report.append("## When to Use This Mode")
        if mode == PerformanceMode.LOW:
            report.append("- **Tutorial and learning:** Simple, easy to understand")
            report.append("- **Area-constrained designs:** Minimal logic")
            report.append("- **Low throughput requirements:** < 40 GB/s")
        elif mode == PerformanceMode.MEDIUM:
            report.append("- **Typical FPGA implementations:** Balanced performance/area")
            report.append("- **Production systems:** Saturates AXI bus with 8 channels")
            report.append("- **Moderate complexity:** Achievable in most designs")
        elif mode == PerformanceMode.HIGH:
            report.append("- **High-end FPGA/ASIC:** Maximum realistic performance")
            report.append("- **Full throughput:** Saturates AXI bus with fewer channels")
            report.append("- **Limited by SRAM:** Cannot improve single-channel performance without more SRAM")
        elif mode == PerformanceMode.PERFECT:
            report.append("- **Theoretical analysis:** Shows ultimate limits")
            report.append("- **Design exploration:** Understand SRAM sizing requirements")
            report.append("- **NOT recommended for implementation:** Excessive SRAM cost")

        report.append("")

        full_report = "\n".join(report)

        if output_file:
            with open(output_file, 'w') as f:
                f.write(full_report)
            print(f"✓ Report saved to {output_file}")

        return full_report

    # Helper methods
    def _explain_pipeline_limit(self, result: Dict, config: AXIConfig) -> str:
        """Explain what limits the effective pipeline depth"""
        if result['effective_pipeline'] == config.pipeline_depth:
            return "configuration"
        elif result['effective_pipeline'] == config.sram_capacity_bursts:
            return "SRAM capacity"
        elif result['effective_pipeline'] == config.max_outstanding:
            return "max outstanding transactions"
        else:
            return "unknown"

    def _explain_bottleneck(self, result: Dict) -> str:
        """Explain the bottleneck in plain English"""
        limited_by = result['limited_by']

        if limited_by == "timing":
            return "Sequential operation - latency dominates"
        elif limited_by == "AXI_peak":
            return "AXI bus saturated (good!)"
        elif limited_by == "SRAM_capacity":
            return "SRAM buffer too small for desired pipeline depth"
        elif limited_by == "max_outstanding":
            return "Outstanding transaction limit"
        else:
            return limited_by

    def _identify_limitations(self, config: StreamDMAConfig,
                             read_1ch: Dict, write_1ch: Dict) -> List[str]:
        """Identify design limitations"""
        limitations = []

        # Pipeline limitations
        if read_1ch['effective_pipeline'] < config.read_config.pipeline_depth:
            limitations.append(f"**Read pipeline limited to {read_1ch['effective_pipeline']}** (desired: {config.read_config.pipeline_depth}) by {self._explain_pipeline_limit(read_1ch, config.read_config)}")

        if write_1ch['effective_pipeline'] < config.write_config.pipeline_depth:
            limitations.append(f"**Write pipeline limited to {write_1ch['effective_pipeline']}** (desired: {config.write_config.pipeline_depth}) by {self._explain_pipeline_limit(write_1ch, config.write_config)}")

        # SRAM capacity
        if read_1ch['limited_by'] == 'SRAM_capacity' or write_1ch['limited_by'] == 'SRAM_capacity':
            limitations.append(f"**SRAM capacity ({config.read_config.sram_lines_per_channel} lines)** insufficient for deep pipelining at current payload size")

        # Throughput
        if read_1ch['efficiency'] < 50:
            limitations.append(f"**Low single-channel efficiency ({read_1ch['efficiency']:.1f}%)** - requires multiple channels to achieve good throughput")

        return limitations

    def _generate_recommendations(self, mode: PerformanceMode, config: StreamDMAConfig,
                                 read_1ch: Dict, write_1ch: Dict, dma_8ch: Dict) -> List[str]:
        """Generate optimization recommendations"""
        recommendations = []

        # Mode-specific recommendations
        if mode == PerformanceMode.LOW:
            recommendations.append("**Upgrade to MEDIUM mode** for 1.5x throughput improvement (37.9 → 57.6 GB/s)")
            recommendations.append("**Add pipelining** to hide memory latency")

        elif mode == PerformanceMode.MEDIUM:
            if dma_8ch['read_efficiency'] >= 99.9:
                recommendations.append("**Already saturating AXI bus** - no further optimization possible without faster interface")
            else:
                recommendations.append("**Increase channels** if not using all 8")

        elif mode == PerformanceMode.HIGH:
            if read_1ch['limited_by'] == 'SRAM_capacity':
                recommendations.append("**Increase SRAM per channel** to enable deeper pipelining for single-channel performance")
                recommendations.append("**Or use multiple channels** to aggregate bandwidth (current strategy)")
            if dma_8ch['read_efficiency'] >= 99.9:
                recommendations.append("**Already saturating AXI bus** with 8 channels")

        elif mode == PerformanceMode.PERFECT:
            recommendations.append("**For analysis only** - 16x SRAM increase (64 KB → 1024 KB) not recommended")
            recommendations.append("**Use channel parallelism instead** (MEDIUM/HIGH modes with multiple channels)")

        # Payload-specific
        if config.read_config.effective_BL < config.read_config.max_burst_len:
            recommendations.append(f"**Increase payload size** to take advantage of larger burst capability ({config.read_config.max_burst_len} beats)")

        return recommendations
