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

# 5.2 Expected Trends

## Per-FUB Sweep Expectations

| FUB | Sweep Parameter | Expected Trend |
|-----|----------------|---------------|
| nand_chain | NAND_LEVELS 1-12 | Linear delay increase per level |
| inverter_chain | INVERTER_COUNT 1-256 | Linear initially, flattens when routing dominates |
| xor_tree | XOR_LEVELS 1-12 | Similar to NAND but fewer logic levels (better LUT packing) |
| carry_chain | CARRY_WIDTH 8-512 | Sub-linear (dedicated carry is fast per bit) |
| multiplier_tree | MULT_WIDTH 8-32 | Quadratic growth (O(n^2) partial products) |
| mux_tree | MUX_LEVELS 1-12 | ~2 levels per LUT on 6-input LUT architectures |
| queue_depth | FIFO_DEPTH 4-4096 | Step changes at LUTRAM/BRAM/URAM boundaries |
| clock_divider_chain | CLK_DIV_STAGES 1-8 | Linear per stage |
| gray_counter_chain | GRAY_WIDTH 4-128 | XOR tree dominates above ~32 bits |

## Cross-FUB Comparisons

At the same tree depth, expected relative delay ordering (fastest to slowest):

1. **inverter_chain** -- Minimal fan-in, best-case routing
2. **xor_tree** -- Good LUT packing for XOR
3. **mux_tree** -- Efficient mux-to-LUT mapping
4. **nand_chain** -- Standard LUT mapping
5. **carry_chain** -- Dedicated carry (fast per bit, but total delay grows with width)

## Technology-Dependent Observations

### FPGA-Specific
- **Carry chains** will show dramatically better per-bit delay than LUT chains
- **Multiplier (TYPE=0)** will use DSP slices on Xilinx, showing a large speed advantage
- **XOR trees** may pack more efficiently than NAND trees (6-LUT absorbs more XOR levels)
- **queue_depth** will show clear transitions at LUTRAM and BRAM boundaries

### ASIC-Specific
- All gate types map to standard cells -- no dedicated carry or DSP
- Delay differences between gate types are smaller
- Routing delay is more predictable
- Multiplier type selection matters more (no DSP shortcut)

## Normalizing Results

To compare across technologies, normalize to **delay per logic level**:

```
delay_per_level = data_path_delay / logic_levels
```

This isolates the per-gate (or per-LUT) delay, which is the true
technology-dependent metric.
