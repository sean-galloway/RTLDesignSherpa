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

# 1.3 Definitions and Acronyms

## Acronyms

| Acronym | Definition |
|---------|-----------|
| ASIC | Application-Specific Integrated Circuit |
| BRAM | Block RAM (dedicated memory on FPGA) |
| CDC | Clock Domain Crossing |
| CSA | Carry-Save Adder |
| DC | Design Compiler (Synopsys synthesis tool) |
| DSP | Digital Signal Processing (dedicated multiplier slice on FPGA) |
| Fmax | Maximum achievable clock frequency |
| FPGA | Field-Programmable Gate Array |
| FUB | Functional Unit Block |
| HAS | Hardware Architecture Specification |
| LFSR | Linear Feedback Shift Register |
| LUT | Look-Up Table (basic FPGA logic element) |
| LUTRAM | Distributed RAM implemented in LUTs |
| MAS | Micro-Architecture Specification |
| SDC | Synopsys Design Constraints (industry-standard timing constraint format) |
| STA | Static Timing Analysis |
| URAM | UltraRAM (high-density memory on Xilinx UltraScale+) |

## Key Terms

| Term | Definition |
|------|-----------|
| **Characterization** | The process of measuring timing, area, or power for a specific logic structure on a specific technology target |
| **Critical path** | The longest combinational delay between two registers, determining maximum frequency |
| **Dont-touch** | Synthesis attribute that prevents the tool from optimizing or restructuring the annotated logic |
| **Logic level** | One stage of combinational logic (one LUT on FPGA, one gate on ASIC) |
| **Parameter sweep** | Running synthesis with varying parameter values to map a performance curve |
| **Setup slack** | Time margin between data arrival and clock edge; negative slack means timing failure |
| **Technology target** | A specific FPGA part number or ASIC standard-cell library |
