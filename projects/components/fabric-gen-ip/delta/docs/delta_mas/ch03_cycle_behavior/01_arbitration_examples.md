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

# Multi-Master Contention

## Scenario

Two masters, M0 and M1, both want to send packets to the same slave S0. S0 is initially idle. M0 sends a two-beat packet; M1 sends a one-beat packet.

## Cycle Trace

Assumption: `last_grant[S0]` was 1 before the trace begins.

| Cycle | Event | `request_matrix[S0]` | `grant_matrix[S0]` | `packet_active[S0]` | Notes |
|-------|-------|----------------------|--------------------|---------------------|-------|
| 0 | M0 and M1 both request S0 | `2'b11` | `2'b00` | 0 | Slave idle. |
| 1 | Arbiter picks M0 (RR after last_grant=1) | `2'b11` | `2'b01` | 1 | Grant registered. |
| 2 | M0 beat 0 accepted | `2'b10` | `2'b01` | 1 | M1 waits. |
| 3 | M0 beat 1 (TLAST) accepted | `2'b10` | `2'b00` | 0 | Packet ends; grant released. |
| 4 | Arbiter picks M1 | `2'b10` | `2'b10` | 1 | M1 now granted. |
| 5 | M1 beat 0 (TLAST) accepted | `2'b00` | `2'b00` | 0 | Both packets complete. |

: Contention Trace

## Observations

- M1 waits while M0 completes its packet.
- The arbiter does not re-arbitrate inside a packet.
- After `TLAST`, the next arbitration cycle grants M1 because M0 was the previous grant.
- Round-robin ensures M1 is not starved.

## Same-Cycle Release and Re-Arbitration

On the cycle that `TLAST` is accepted, the grant is released. The next rising edge can register a new grant if a request is pending. This gives a one-cycle gap between back-to-back packets from different masters.
