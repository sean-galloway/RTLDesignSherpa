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

# 1.2 Document Conventions

## Signal Naming

| Prefix | Meaning | Example |
|--------|---------|---------|
| `r_` | Registered (flip-flop output) | `r_lfsr`, `r_input_a` |
| `w_` | Wire (combinational) | `w_chain`, `w_sum` |
| `i_` | Input port | `i_seed_data` |
| `o_` | Output port | `o_carry` |
| `EN_` | Enable parameter | `EN_CARRY_CHAIN` |
| `gen_` | Generate block label | `gen_carry` |

## Parameter Naming

All configurable parameters use `UPPER_CASE` naming:

- **Feature enables:** `EN_{FUB_NAME}` (1 = enabled, 0 = disabled)
- **Depth/width:** `{FUB}_{DIMENSION}` (e.g., `CARRY_WIDTH`, `NAND_LEVELS`)
- **Type selectors:** `{FUB}_TYPE` (e.g., `MULT_TYPE`)

## RTL Conventions

- **Reset:** Active-low asynchronous (`rst_n`), using `ALWAYS_FF_RST` macros
- **Clock:** Single clock domain (`clk`)
- **Synthesis attributes:** `dont_touch` (Xilinx) / `preserve` (Intel) on chain signals
- **Array syntax:** `[DEPTH]` (not `[0:DEPTH-1]`)

## Document Structure

- **HAS (this document):** System-level architecture, interfaces, performance
- **MAS (companion):** Block-level micro-architecture, LFSR design, implementation detail
