<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# 5.1 Synthesis Targets

## Target Frequency

The default SDC target is **500 MHz** (2.0 ns period). This is intentionally
aggressive for most FPGA fabrics and will produce negative setup slack for
deeper combinational paths. The negative slack is the primary measurement --
it directly quantifies how far each FUB falls short of the target.

## Supported Technology Targets

| Category | Example Targets | Tool |
|----------|----------------|------|
| Xilinx 7-series | Artix-7 (xc7a200t), Kintex-7 (xc7k325t) | Vivado |
| Xilinx UltraScale+ | VU9P (xcvu9p), KU15P (xcku15p) | Vivado |
| Intel Cyclone | Cyclone 10 LP, Cyclone V | Quartus Prime |
| Intel Stratix | Stratix 10, Agilex | Quartus Prime |
| ASIC | TSMC 28nm, GF 22nm, Samsung 14nm | DC / Genus |

## Frequency Sweep Points

For comprehensive characterization, sweep these frequencies:

| Frequency (MHz) | Period (ns) | Typical Use |
|-----------------|-------------|-------------|
| 100 | 10.0 | Low-speed baseline (most paths pass) |
| 200 | 5.0 | Moderate speed |
| 300 | 3.33 | Common FPGA target |
| 400 | 2.5 | High-performance FPGA |
| 500 | 2.0 | Aggressive (default SDC target) |
| 600 | 1.67 | Very aggressive |
| 750 | 1.33 | Near physical limit for most FPGAs |
| 1000 | 1.0 | Theoretical limit exploration |

## Key Metrics Per Run

| Metric | Source | Meaning |
|--------|--------|---------|
| **Setup slack** | Timing report | Margin to clock edge (negative = fails) |
| **Data path delay** | Timing report | Actual combinational delay in nanoseconds |
| **Logic levels** | Timing report | Number of LUT/gate levels traversed |
| **Fmax** | Computed: `1 / (period - slack)` | Maximum achievable frequency |
| **Resource usage** | Utilization report | LUTs, FFs, DSPs, BRAMs consumed |
