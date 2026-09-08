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

# 5.3 Resource Estimates

## FPGA Resource Usage (All FUBs Enabled, Default Parameters)

These are approximate estimates for Xilinx 7-series at default parameters:

| Resource | Estimated Usage | Primary Contributors |
|----------|----------------|---------------------|
| LUTs | ~500-800 | Tree FUBs, FIFO control logic |
| Flip-Flops | ~200-300 | LFSR (32), FUB input/output flops |
| DSP48 | 0 or 1 | multiplier_tree (TYPE=0 at small width may use DSP) |
| BRAM | 0 or 1 | queue_depth (depends on FIFO_DEPTH) |
| Carry chains | ~8-64 bits | carry_chain, gray_counter_chain counters |

## Per-FUB Resource Breakdown

| FUB | LUTs (approx) | FFs (approx) | Special |
|-----|---------------|-------------|---------|
| nand_chain | 2^LEVELS - 1 | LEVELS + 1 | -- |
| inverter_chain | INVERTER_COUNT | 2 | -- |
| xor_tree | 2^LEVELS - 1 | LEVELS + 1 | -- |
| carry_chain | CARRY_WIDTH | 3*WIDTH + 1 | Carry chain |
| multiplier_tree | WIDTH^2 (structural) | 3*WIDTH | DSP (TYPE=0) |
| mux_tree | 2^LEVELS - 1 | LEVELS + NUM_FLOPS | -- |
| queue_depth | DEPTH * WIDTH (LUTRAM) | ~20 | BRAM at large depth |
| clock_divider_chain | STAGES * CW | STAGES * CW | -- |
| gray_counter_chain | 2 * WIDTH | 2 * WIDTH | Carry chain |

## Scaling Considerations

Resource usage scales differently for each FUB:

- **Tree FUBs** (nand, xor, mux): Exponential with LEVELS (`O(2^L)`)
- **Linear FUBs** (inverter): Linear with COUNT (`O(N)`)
- **Arithmetic FUBs** (carry): Linear with WIDTH (`O(W)`)
- **Multiplier**: Quadratic with WIDTH (`O(W^2)`) for structural types
- **FIFO**: Linear with DEPTH * WIDTH for LUTRAM; constant for BRAM

The characterization harness is intentionally small. Even with all FUBs
enabled at default parameters, it consumes a negligible fraction of any
modern FPGA or ASIC target.
