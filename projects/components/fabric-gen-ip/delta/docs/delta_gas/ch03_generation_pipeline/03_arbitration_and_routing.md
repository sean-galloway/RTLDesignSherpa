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

# Arbitration and Routing

## Packet-atomic round-robin arbitration

Unlike the APB crossbar, which re-arbitrates every cycle, Delta locks the grant until the end of the current packet. This prevents interleaving beats from different masters on the same slave.

```systemverilog
logic [NUM_MASTERS-1:0] grant_matrix [NUM_SLAVES];
logic [$clog2(NUM_MASTERS)-1:0] last_grant [NUM_SLAVES];
logic packet_active [NUM_SLAVES];
```

Arbitration state machine for each slave:

1. If `packet_active[s]` is true, hold the grant until `m_axis_tvalid[s] && m_axis_tready[s] && m_axis_tlast[s]`.
2. If no packet is active and `request_matrix[s]` is non-zero, choose the next requesting master in round-robin order after `last_grant[s]`.
3. Set `packet_active[s]` when a new grant is awarded.

## Crossbar mux

A per-slave `always_comb` block muxes the granted master's AXI-Stream signals to the slave output:

```systemverilog
for (int m = 0; m < NUM_MASTERS; m++)
    if (grant_matrix[s][m]) begin
        m_axis_tdata[s]  = s_axis_tdata[m];
        m_axis_tvalid[s] = s_axis_tvalid[m];
        m_axis_tlast[s]  = s_axis_tlast[m];
        m_axis_tdest[s]  = s_axis_tdest[m];
        m_axis_tid[s]    = s_axis_tid[m];
        m_axis_tuser[s]  = s_axis_tuser[m];
        // TSTRB included when enabled; with --amba5 the payload check
        // bits (TDATACHK..TUSERCHK) ride the same grant, carried unchanged
    end
```

## Backpressure routing

Each master's `s_axis_tready` is driven from the `m_axis_tready` of the slave to which it is currently granted:

```systemverilog
for (int m = 0; m < NUM_MASTERS; m++) begin
    s_axis_tready[m] = 1'b0;
    for (int s = 0; s < NUM_SLAVES; s++)
        if (grant_matrix[s][m])
            s_axis_tready[m] = m_axis_tready[s];
end
```

This preserves AXI-Stream ready/valid handshake semantics across the switch.
