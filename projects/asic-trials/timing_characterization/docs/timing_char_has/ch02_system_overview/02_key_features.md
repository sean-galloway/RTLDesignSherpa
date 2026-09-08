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

# 2.2 Key Features

## Feature Summary

| Feature | Description |
|---------|-------------|
| **9 independent FUBs** | Each targets a different class of combinational logic |
| **Selective enable** | EN_* parameters allow single-FUB or mixed synthesis |
| **Shared LFSR** | 32-bit Galois LFSR prevents constant propagation |
| **Multi-flow SDC** | Single constraint file supports ASIC, Vivado, Quartus |
| **Parameterized depth** | Every FUB has sweep-friendly depth/width parameters |
| **Anti-optimization** | LFSR + dont_touch + port routing prevents synthesis shortcuts |
| **Self-contained** | All dependencies included in component directory |
| **Functionally verified** | 45 CocoTB tests confirm correct operation |

## Logic Family Coverage

The nine FUBs cover the major combinational logic families encountered in production designs:

| Logic Family | FUB | FPGA Resource |
|-------------|-----|---------------|
| Basic gates (NAND) | nand_chain | LUT fabric |
| Pure delay (inverter) | inverter_chain | LUT fabric |
| Arithmetic (XOR) | xor_tree | LUT fabric |
| Fast carry | carry_chain | Dedicated carry chain |
| Multiplication | multiplier_tree | DSP slices or LUT fabric |
| Selection (mux) | mux_tree | LUT fabric |
| Storage | queue_depth | LUTRAM / BRAM / URAM |
| Clock generation | clock_divider_chain | Counter + LUT |
| Encoding | gray_counter_chain | Counter + XOR tree |

## Synthesis Tool Support

| Tool | Flow Name | Constraint Format |
|------|-----------|------------------|
| Synopsys Design Compiler | `asic` | SDC (source) |
| Cadence Genus | `asic` | SDC (read_sdc) |
| Xilinx Vivado | `vivado` | SDC/XDC (read_xdc) |
| Intel Quartus Prime | `quartus` | SDC (set_global_assignment) |
