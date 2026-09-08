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

# 4.1 Top-Level Ports

## Input Ports

| Port | Width | Description |
|------|-------|-------------|
| `clk` | 1 | System clock |
| `rst_n` | 1 | Active-low asynchronous reset |
| `i_seed_valid` | 1 | LFSR seed load strobe |
| `i_seed_data` | 32 | LFSR seed value |

## Output Ports

| Port | Width | Source FUB | Description |
|------|-------|-----------|-------------|
| `o_nand` | 1 | nand_chain | NAND tree output |
| `o_inverter` | 1 | inverter_chain | Inverter chain output |
| `o_xor` | 1 | xor_tree | XOR tree output |
| `o_carry` | CARRY_WIDTH+1 | carry_chain | Adder sum (includes carry-out) |
| `o_mult` | 2*MULT_WIDTH | multiplier_tree | Multiplier product |
| `o_mux` | 1 | mux_tree | Mux tree output |
| `o_queue_data` | FIFO_DATA_WIDTH | queue_depth | FIFO read data |
| `o_queue_valid` | 1 | queue_depth | FIFO read valid |
| `o_queue_count` | varies | queue_depth | FIFO occupancy count |
| `o_clk_div` | CLK_DIV_STAGES | clock_divider_chain | Divided clock outputs |
| `o_gray_bin` | GRAY_WIDTH | gray_counter_chain | Binary counter value |
| `o_gray_code` | GRAY_WIDTH | gray_counter_chain | Gray code value |

## Port Behavior When FUB Disabled

When a FUB is disabled via its `EN_*` parameter, the corresponding output
ports are tied to zero:

```systemverilog
assign o_carry = '0;  // When EN_CARRY_CHAIN = 0
```

This ensures the output port widths remain consistent regardless of which FUBs
are enabled, simplifying synthesis scripts and constraint files.
