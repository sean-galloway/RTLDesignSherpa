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

# Packet Interleave Prevention

## Rule

A slave can source data from only one master within a single packet. The grant is locked from the first beat of the packet until the `TLAST` beat is accepted.

## Mechanism

The `packet_active[s]` flag is set when a new grant is made. While `packet_active[s]` is high:

- `grant_matrix[s]` is held constant.
- The crossbar mux continues to select the same master.
- `s_axis_tready` for the granted master follows only `m_axis_tready[s]`.

When `m_axis_tvalid[s] && m_axis_tready[s] && m_axis_tlast[s]` is true, `packet_active[s]` clears and the grant is released.

## Why It Matters

AXI4-Stream slaves often expect packet-atomic streams. If beats from different masters were interleaved, a slave receiving the mixed stream could misinterpret packet boundaries, corrupt state, or violate protocol.

## Example: Attempted Interleave

Suppose M0 and M1 both target S0 and both have multi-beat packets:

| Cycle | Without atomicity (hypothetical) | With Delta packet atomicity |
|-------|----------------------------------|------------------------------|
| 0 | M0 beat 0 | M0 beat 0 |
| 1 | M1 beat 0 (interleaved!) | M0 beat 1 |
| 2 | M0 beat 1 | M0 beat 2 (TLAST) |
| 3 | M1 beat 1 (TLAST) | M1 beat 0 |

: Interleave Prevention

Delta prevents the interleaved case by holding M0's grant until its `TLAST`.

## Corner Cases

- If the granted master drops `TVALID` mid-packet, the slave sees no valid beats until the master reasserts it. The grant is still held.
- If the downstream slave is never ready, the packet can stall indefinitely; there is no timeout. This is consistent with standard AXI4-Stream behavior.
