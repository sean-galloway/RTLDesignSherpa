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

# 1.1 Overview

## Component Summary

The Timing Characterization component consists of:

- **1 top-level wrapper** (`char_top.sv`) with a shared 32-bit Galois LFSR
- **9 Functional Unit Blocks** (FUBs), each targeting a different class of
  combinational logic
- **1 standalone wrapper** (`nand_chain_top.sv`) for isolated NAND chain synthesis
- **26 shared dependency modules** copied from `rtl/common/`
- **1 multi-flow SDC** constraint file supporting ASIC, Vivado, and Quartus

## Module Inventory

| Module | File | Type | Description |
|--------|------|------|-------------|
| `char_top` | `rtl/top/char_top.sv` | Top-level | 9-FUB wrapper with shared LFSR |
| `nand_chain_top` | `rtl/top/nand_chain_top.sv` | Top-level | Standalone NAND chain |
| `nand_chain` | `rtl/fub/nand_chain.sv` | FUB | NAND gate binary tree |
| `inverter_chain` | `rtl/fub/inverter_chain.sv` | FUB | Linear inverter chain |
| `xor_tree` | `rtl/fub/xor_tree.sv` | FUB | XOR gate binary tree |
| `carry_chain` | `rtl/fub/carry_chain.sv` | FUB | Ripple-carry adder |
| `multiplier_tree` | `rtl/fub/multiplier_tree.sv` | FUB | Multiplier (5 types) |
| `mux_tree` | `rtl/fub/mux_tree.sv` | FUB | Binary mux tree |
| `queue_depth` | `rtl/fub/queue_depth.sv` | FUB | FIFO queue |
| `clock_divider_chain` | `rtl/fub/clock_divider_chain.sv` | FUB | Clock divider cascade |
| `gray_counter_chain` | `rtl/fub/gray_counter_chain.sv` | FUB | Gray counter |

## Common FUB Structure

Every FUB follows an identical structural pattern:

```systemverilog
module fub_name #(parameter int DEPTH = N) (
    input  logic clk,
    input  logic rst_n,
    input  logic [...] i_data,    // From LFSR taps (combinational)
    output logic [...] o_data     // To top-level port
);
    // Stage 1: Input register(s)
    logic [...] r_input;
    `ALWAYS_FF_RST(clk, rst_n, ...)

    // Stage 2: Combinational logic under test
    // (* dont_touch = "true" *) or /* synthesis preserve */
    logic [...] w_result;
    // ... combinational logic ...

    // Stage 3: Output register
    logic [...] r_output;
    `ALWAYS_FF_RST(clk, rst_n, ...)

    assign o_data = r_output;
endmodule
```

This 3-stage pattern (input FF -> combinational -> output FF) ensures all
critical paths are register-to-register.
