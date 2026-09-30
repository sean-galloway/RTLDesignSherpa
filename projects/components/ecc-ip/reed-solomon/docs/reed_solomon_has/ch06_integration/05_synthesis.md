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

# Synthesis and Implementation

## Characterisation plan

Numbers in chapter 5 are analytic. They are replaced by measurements the
way the repository measures every other block: an out-of-context synthesis
fixture per configuration, on the same two parts the monitor and bridge
characterisations use.

| Step | Fixture | Output |
|---|---|---|
| 1 | `rs_encoder_core` and `rs_decoder_core`, reference profile, S = 1, Artix-7 100T -1 at 10 ns and Kintex-7 325T -2 at 6.667 ns | LUTs, flops, BRAM, WNS; the calibration for table 5.5 |
| 2 | decoder with `KES_ALGO = "EUCLID"` | the solver comparison in table 3.1 measured |
| 3 | S = 2, 4, 8 | the scaling in table 5.2 measured; the Forney stall design decided |
| 4 | CCSDS and 802.3 profiles | t and m scaling |
| 5 | standalone tops with each adapter pair | adapter cost; the monitors' cost is already known |

: Table 6.6: Characterisation steps

The fixture follows `projects/components/fabric-gen-ip/bridge/fpga/`
(`make synth BRIDGE=<fixture>` on `make/fpga_flow.mk`) and reports through
the same `summary.csv` shape, so the numbers land beside the bridge's and
the monitor's.

## Implementation notes

- All arithmetic is combinational XOR/AND networks; there are no carries,
  so the multiplier trees of `rtl/math` do not apply and the synthesiser's
  DSP inference is irrelevant.
- `gf_inv` at m = 8 is two 256-entry ROMs and infers to LUTs; at m = 10 it
  becomes BRAM or Itoh-Tsujii.
- The block buffer infers one BRAM at the reference depth; `REGISTERED = 1`
  on the FIFO adds a cycle and removes the read mux from the corrector's
  path if timing needs it.
- The riBM array has no cross-array feedback, so its cells may be
  pipelined per iteration if the clock demands; the Euclid array's degree
  compare cannot be pipelined without the degree-computationless variant.
- No clock gating in the core; boundary gating comes from the `_cg` wrapper
  variants at the adapters.
