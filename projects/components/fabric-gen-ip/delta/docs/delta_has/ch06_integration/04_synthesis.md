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

# Synthesis and Implementation

## Synthesis Flow

The generated module is a flat SystemVerilog file intended for standard synthesis:

```bash
# Example Vivado flow
read_verilog rtl/delta_axis_flat_4x16.sv
synth_design -top delta_axis_flat_4x16 -part xczu7ev-ffvc1156-2-e
```

## Timing Considerations

- The critical path is typically from `s_axis_tvalid/tdest` through the decode and mux to `m_axis_tdata/tvalid`.
- Because the grant is registered, the mux select is stable for a full cycle once a grant is made.
- The `TREADY` path is combinational from `m_axis_tready` to `s_axis_tready`.

## Floorplanning Suggestions

- For large crossbars, consider registering `s_axis_tdata` at the master boundary if the combinational mux path is too long.
- Keep related master/slave groups physically close to reduce routing congestion.
- If Fmax is insufficient, the generator supports `--no-counters` and reduced `DATA_WIDTH` to ease timing.

## Implementation Checklist

- [ ] Synthesize the generated module in the target tool.
- [ ] Check setup/hold timing on `aclk`.
- [ ] Verify `aresetn` deassertion is synchronous to `aclk`.
- [ ] Run a post-implementation functional simulation if the design is modified after generation.
