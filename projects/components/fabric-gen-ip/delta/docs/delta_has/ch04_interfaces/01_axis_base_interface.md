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

# AXI-Stream Base Interface

## Master Interface (S_AXIS)

Each master port is indexed by `m` in the range `0` to `NUM_MASTERS-1`.

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `s_axis_tdata[m]` | `DATA_WIDTH` | Input | Data payload. |
| `s_axis_tvalid[m]` | 1 | Input | Valid indicator. When high, `s_axis_tdest[m]` selects the target slave. |
| `s_axis_tready[m]` | 1 | Output | Ready / backpressure. Driven from the granted slave's `m_axis_tready`. |
| `s_axis_tlast[m]` | 1 | Input | Packet boundary. The final beat of a packet. |
| `s_axis_tdest[m]` | `DEST_WIDTH` | Input | Target slave index. Must be `< NUM_SLAVES` when `tvalid` is asserted. |
| `s_axis_tid[m]` | `ID_WIDTH` | Input | Transaction ID. Pass-through to `m_axis_tid`. |
| `s_axis_tuser[m]` | `USER_WIDTH` | Input | User sideband. Pass-through to `m_axis_tuser`. |

: Table 4.1: Base Master Interface Signals

## Slave Interface (M_AXIS)

Each slave port is indexed by `s` in the range `0` to `NUM_SLAVES-1`.

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `m_axis_tdata[s]` | `DATA_WIDTH` | Output | Data payload from the granted master. |
| `m_axis_tvalid[s]` | 1 | Output | Valid indicator. Asserted when a grant is active and the selected master is valid. |
| `m_axis_tready[s]` | 1 | Input | Ready / backpressure from the downstream slave. |
| `m_axis_tlast[s]` | 1 | Output | Packet boundary. Forwarded from the granted master. |
| `m_axis_tdest[s]` | `DEST_WIDTH` | Output | Target slave index. Pass-through from the granted master. |
| `m_axis_tid[s]` | `ID_WIDTH` | Output | Transaction ID. Pass-through from the granted master. |
| `m_axis_tuser[s]` | `USER_WIDTH` | Output | User sideband. Pass-through from the granted master. |

: Table 4.2: Base Slave Interface Signals

## Signal Semantics

- `TVALID` may be asserted without `TREADY`; the transfer completes only when both are high.
- `TREADY` for an ungranted master is always low.
- `TDEST` must be stable while `TVALID` is asserted and the master is waiting for grant or transfer.
- `TID` and `TUSER` are pass-through and must be stable on every valid beat.
