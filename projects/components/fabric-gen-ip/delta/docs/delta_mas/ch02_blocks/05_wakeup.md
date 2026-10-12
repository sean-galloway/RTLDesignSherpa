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

# TWAKEUP Steering (AMBA5)

## Purpose

When `--amba5` is enabled, the generated module includes `s_axis_twakeup` and `m_axis_twakeup` ports. `TWAKEUP` is an AMBA 5 hint that a master will soon send a transaction; it may assert before `TVALID`.

## Implementation

The wakeup steering is combinational and independent of the grant:

```systemverilog
always_comb begin
    for (int s = 0; s < NUM_SLAVES; s++) begin
        m_axis_twakeup[s] = 1'b0;
        for (int m = 0; m < NUM_MASTERS; m++) begin
            if (s_axis_twakeup[m] &&
                (s_axis_tdest[m] == s[$clog2(NUM_SLAVES)-1:0])) begin
                m_axis_twakeup[s] = 1'b1;
            end
        end
    end
end
```

## Semantics

- `m_axis_twakeup[s]` is the OR of `s_axis_twakeup[m]` from every master whose `TDEST` points to slave `s`.
- No grant is required; the hint is decoded directly from `TDEST`.
- `TWAKEUP` may be high while `TVALID` is low.
- The hint is not a handshake; the slave is not required to respond before data arrives.

## Integration Notes

- `TWAKEUP` is only emitted when `--amba5` is specified.
- `--amba5` also emits `TWAKEUPCHK`. The crossbar generates `m_axis_twakeupchk[s]` from this OR and checks `s_axis_twakeupchk[m]`. See Interface Check Signals (AMBA5).
- `TWAKEUP` does not affect arbitration timing.
