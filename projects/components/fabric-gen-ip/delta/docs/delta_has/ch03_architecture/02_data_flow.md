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

# Data Flow

## Request Flow

1. A master asserts `s_axis_tvalid[m]` and places the target slave index on `s_axis_tdest[m]`.
2. The TDEST decode block sets `request_matrix[s][m]` for the selected slave.
3. If the slave is not already serving another packet, the per-slave round-robin arbiter grants one requesting master.
4. The grant is registered and held until the packet ends on `TLAST`.

## Payload Flow

1. While a grant is active, the crossbar mux selects the granted master's payload.
2. `m_axis_tdata[s]`, `m_axis_tlast[s]`, `m_axis_tdest[s]`, `m_axis_tid[s]`, and `m_axis_tuser[s]` are driven from the granted master.
3. If `TSTRB` is enabled, `m_axis_tstrb[s]` is also forwarded.
4. If `TPARITY` is enabled, `m_axis_tparity[s]` is forwarded.

## Backpressure Flow

1. Each downstream slave drives `m_axis_tready[s]`.
2. The TREADY steering block routes the granted slave's ready back to the owning master.
3. Only the granted master sees `s_axis_tready[m] == 1`; all other masters are stalled.

## Wakeup Flow (AMBA5)

1. A master may assert `s_axis_twakeup[m]` before asserting `s_axis_tvalid[m]`.
2. The TWAKEUP steering block decodes `s_axis_tdest[m]` and ORs the hint to the matching slave.
3. `m_axis_twakeup[s]` may assert with no active grant.

## Packet Boundaries

`TLAST` marks the final beat of a packet. The arbiter releases the grant on the cycle in which `m_axis_tvalid[s] && m_axis_tready[s] && m_axis_tlast[s]` is true. The next arbitration decision can occur on the following cycle.
