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

# TREADY Steering

## Purpose

TREADY steering routes each slave's `m_axis_tready` back to the master that currently holds the grant for that slave. Ungranted masters see `s_axis_tready[m] == 0`.

## Implementation

```systemverilog
generate
    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_master_tready
        always_comb begin
            s_axis_tready[m] = 1'b0;
            for (int s = 0; s < NUM_SLAVES; s++) begin
                if (grant_matrix[s][m]) begin
                    s_axis_tready[m] = m_axis_tready[s];
                end
            end
        end
    end
endgenerate
```

## Behavior

- Only one slave can grant a given master at a time (packets are atomic and a master targets one slave per packet), so the loop effectively selects a single `m_axis_tready[s]`.
- If a master is not currently granted by any slave, it is stalled.
- Backpressure propagates combinationally from slave to master.

## Deadlock Avoidance

The design avoids deadlock because:

- Grants are released after `TLAST`, freeing the slave for new requests.
- `TREADY` is combinationally steered; a slave ready transition immediately reaches the granted master.
- There are no FIFOs or credit loops in the base crossbar.
