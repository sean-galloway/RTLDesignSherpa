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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Lint Checks

The generated RTL must pass the project's lint flow. The most common lint concerns for generated crossbars are width mismatches and unused signals.

## Width checks

- `slave_addr_bits` is `ceil(log2(num_slaves))` and is at least 1.
- `slave_offset_bits` is `log2(slave_size)` and is used to slice the offset.
- The `BASE_ADDR` parameter is `ADDR_WIDTH` bits.
- APB5 sideband signals are 1-bit logic; parity vectors are `STRB_WIDTH` or 1 bit as appropriate.

## Unused signal checks

When parity is disabled on an APB5 port, the generator leaves some output pins unconnected. The lint waiver for these is part of the boundary module, not the generated crossbar. Ensure the waiver file or lint command set covers `apb5_slave` and `apb5_master` tie-offs.

## Synthesis smoke test

As a minimum sanity check, run a synthesis tool on the 2×4 variant after any generator change. The expected result is clean elaboration with no latch inference and no combinational loops.
