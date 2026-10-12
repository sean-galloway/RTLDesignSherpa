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

# Flat Crossbar

The flat crossbar is the production artifact. It is a single module that connects any master to any slave based on `TDEST`.

## Internal structures

| Signal / Variable | Purpose |
|-------------------|---------|
| `request_matrix[NUM_SLAVES]` | One-hot request vector per slave. |
| `grant_matrix[NUM_SLAVES]` | One-hot grant vector per slave. |
| `last_grant[NUM_SLAVES]` | Round-robin pointer per slave. |
| `packet_active[NUM_SLAVES]` | Lock grant until `TLAST`. |

## Optional features

### Performance counters

When `add_performance_counters=True`, the generator emits 32-bit packet counters:

```systemverilog
logic [31:0] pkt_count_master [NUM_MASTERS];
logic [31:0] pkt_count_slave [NUM_SLAVES];
```

Counters increment on `valid && ready && tlast` at the master or slave interface.

### Assertions

Under `` `ifdef FORMAL ``:

- One-hot grant check per slave.
- TDEST range check per master.

These assertions are intended for formal verification flows and are stripped during normal simulation if `FORMAL` is not defined.
