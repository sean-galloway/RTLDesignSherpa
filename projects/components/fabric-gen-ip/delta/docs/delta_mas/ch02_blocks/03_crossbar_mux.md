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

# Crossbar Multiplexer

## Purpose

The crossbar mux selects the payload and control signals from the granted master and drives them onto the selected slave interface. There is one mux per slave.

## Implementation

Each slave mux is combinational:

```systemverilog
generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_slave_mux
        always_comb begin
            m_axis_tdata[s]  = '0;
            m_axis_tvalid[s] = 1'b0;
            m_axis_tlast[s]  = 1'b0;
            m_axis_tdest[s]  = '0;
            m_axis_tid[s]    = '0;
            m_axis_tuser[s]  = '0;

            for (int m = 0; m < NUM_MASTERS; m++) begin
                if (grant_matrix[s][m]) begin
                    m_axis_tdata[s]  = s_axis_tdata[m];
                    m_axis_tvalid[s] = s_axis_tvalid[m];
                    m_axis_tlast[s]  = s_axis_tlast[m];
                    m_axis_tdest[s]  = s_axis_tdest[m];
                    m_axis_tid[s]    = s_axis_tid[m];
                    m_axis_tuser[s]  = s_axis_tuser[m];
                end
            end
        end
    end
endgenerate
```

## Signal Selection

The mux forwards the following signals from the granted master to the selected slave:

- `TDATA`
- `TVALID`
- `TLAST`
- `TDEST`
- `TID`
- `TUSER`
- `TSTRB` (when enabled)
- The payload check bits `TDATACHK`, `TSTRBCHK`, `TLASTCHK`, `TIDCHK`, `TDESTCHK`, `TUSERCHK` (with `--amba5`). They are carried unchanged, not regenerated. See Interface Check Signals (AMBA5).

## Default Values

When no grant is active for a slave, the mux drives all outputs to zero and `m_axis_tvalid[s]` to low. This is a safe idle state. With `--amba5`, the payload check outputs idle at all ones instead, which is the odd parity of the all-zero idle payload.

## Timing

Because the mux is combinational, the output settles after the grant and the input signals are stable. The grant is registered, so the mux select is stable for a full clock cycle once a packet begins.
