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

# Request Decode

## Purpose

The request decode block translates each master's `s_axis_tvalid` and `s_axis_tdest` into a per-slave request matrix. A set bit in `request_matrix[s][m]` indicates that master `m` is requesting slave `s`.

## Implementation

The decode is combinational:

```systemverilog
logic [NUM_MASTERS-1:0] request_matrix [NUM_SLAVES];

always_comb begin
    for (int s = 0; s < NUM_SLAVES; s++) begin
        request_matrix[s] = '0;
    end
    for (int m = 0; m < NUM_MASTERS; m++) begin
        if (s_axis_tvalid[m] &&
            (s_axis_tdest[m] < NUM_SLAVES[$clog2(NUM_SLAVES+1)-1:0])) begin
            request_matrix[s_axis_tdest[m]][m] = 1'b1;
        end
    end
end
```

## TDEST Range Check

The comparison `s_axis_tdest[m] < NUM_SLAVES` prevents out-of-range indices from corrupting the `request_matrix` array. The width of the comparison is sized to cover the full `NUM_SLAVES` value.

## Relationship to Arbitration

The request matrix is the input to each slave's round-robin arbiter. Only slaves with at least one request bit set are candidates for a new grant.

## Notes

- The decode does not depend on `TREADY`; a master may request even while stalled.
- `TDEST` is sampled combinationally and must be stable while `TVALID` is asserted.
- There is no address map; `TDEST` is the slave index directly.
