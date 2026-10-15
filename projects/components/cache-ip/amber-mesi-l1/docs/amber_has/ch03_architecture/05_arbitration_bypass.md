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

# Arbitration and the Victim Bypass

## Dual-port array arbitration

`l1_tag_array` and `l1_data_array` are dual-port `sdpram_core` instances:

- **Port A** serves CPU lookups, fill writes, and replay reads.
- **Port B** serves snoop lookups and snoop data readout.

The arrays themselves need no arbitration in the common case because CPU and snoop use separate ports. The arbitration problem is at the control level: the miss FSM and the snoop FSM may both need to advance tag state or start a fill/drain in the same cycle. `l1_control` resolves this with snoop-priority round-robin: a snoop is never starved, and a CPU miss waits a bounded number of cycles.

## Victim bypass

`l1_victim` is a depth-1 buffer. When a miss evicts a dirty line, the line is staged while the fill is outstanding. If a snoop arrives for that victim line before the drain completes, the buffer can supply the data without re-reading the array. This is the victim bypass. It is shallow by design: depth 1 matches the single-outstanding miss model and keeps the formal surface small.

## Liveness target

Under fair arbitration, neither snoops nor CPU misses can deadlock. The SymbiYosys proof set (D9) includes a no-deadlock / no-livelock target scoped to `l1_control`, `l1_snoop_resp`, the pending-fill bypass, and the victim handoff, proven at the tiny 16-set / 2-way geometry.

## Pending-fill snoop grant: the PF_GUARD guard

A snoop matching the pending fill is granted against the fill's data only
when the fill is actually in flight — its AR accepted and the response phase
begun. `PF_GUARD` (parameter on `l1_control`/`l1_core`, default `1'b0`, set
to `1` by `amber_top`) enforces this: pre-acceptance, the snoop is answered
from the installed tag state instead. Without the guard, a fill whose AR is
still seeking acceptance promised beats it could never deliver while a
fabric parked waiting for this very snoop's response — the pair-rig deadlock
of amber BUG-002 (commit `ab308d108`). Standalone benches without such a
fabric leave `PF_GUARD=0` and keep the classic bypass behavior. See MAS
ch02_blocks/02 for the cycle-level contract.
