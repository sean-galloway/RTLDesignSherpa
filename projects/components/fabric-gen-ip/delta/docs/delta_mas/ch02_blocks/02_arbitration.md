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

# Per-Slave Round-Robin Arbiter

## State Variables

Each slave `s` maintains three registered variables:

| Variable | Width | Purpose |
|----------|-------|---------|
| `grant_matrix[s]` | `NUM_MASTERS` bits | One-hot (or zero-hot) grant vector. |
| `last_grant[s]` | `clog2(NUM_MASTERS)` bits | Pointer to the most recently granted master. |
| `packet_active[s]` | 1 bit | Set while a packet is in progress on this slave. |

: Arbiter State Variables

## FSM Behavior

The arbiter has two operational states for each slave:

### Idle State (`packet_active[s] == 0`)

- If `request_matrix[s]` is non-zero, perform round-robin arbitration.
- The search starts at `last_grant[s] + 1` and wraps through all masters.
- The first requesting master is granted; `last_grant[s]` is updated and `packet_active[s]` is set.
- If no master requests, `grant_matrix[s]` remains zero.

### Active State (`packet_active[s] == 1`)

- The current grant is held.
- On the cycle where `m_axis_tvalid[s] && m_axis_tready[s] && m_axis_tlast[s]` is true, `packet_active[s]` is cleared and `grant_matrix[s]` is reset to zero.
- If `TLAST` is accepted, the next cycle may re-arbitrate for a new master.

## Round-Robin Pseudocode

```systemverilog
if (packet_active[s]) begin
    if (m_axis_tvalid[s] && m_axis_tready[s] && m_axis_tlast[s]) begin
        packet_active[s] <= 1'b0;
        grant_matrix[s]  <= '0;
    end
end else if (|request_matrix[s]) begin
    grant_matrix[s] = '0;
    for (int i = 0; i < NUM_MASTERS; i++) begin
        int m = (last_grant[s] + 1 + i) % NUM_MASTERS;
        if (request_matrix[s][m] && grant_matrix[s] == '0) begin
            grant_matrix[s][m] = 1'b1;
            last_grant[s]      = m[$clog2(NUM_MASTERS)-1:0];
            packet_active[s]   = 1'b1;
        end
    end
end else begin
    grant_matrix[s] <= '0;
end
```

## Fairness

Round-robin guarantees that no requesting master is starved. The longest wait for a contending master is bounded by the number of other contending masters and the length of their packets.

## Reset Behavior

On reset:

- `grant_matrix[s] <= '0`
- `last_grant[s] <= '0`
- `packet_active[s] <= 1'b0`
