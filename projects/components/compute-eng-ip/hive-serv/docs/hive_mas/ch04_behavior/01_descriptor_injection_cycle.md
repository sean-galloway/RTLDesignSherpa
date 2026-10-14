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

# The Descriptor Injection Cycle, Step by Step

The defining HIVE-C operation: one descriptor from firmware decision to
RAPIDS FIFO. Target: < 30 cycles `hive_c_clk` → RAPIDS accept.

```
Cycle  Action
  1    Firmware completes a descriptor_t write to the mailbox; doorbell pulse.
  2    descriptor_gen pops the record; field assembly (HAS §4.2); tuser/tdest/last fixed.
  3    Record pushed to injection queue; queue occupancy +1 (observation).
 4-6   Injection queue at head; CDC FIFO (hive_c_clk side) accepts; tvalid/tready handshake.
 7-10  Gray-pointer cross to delta_clk side; FIFO output registered.
11-20  Delta traversal toward virtual tile 16 (router hops; ~2/hop, edge-attached).
21-24  RAPIDS ingress handshake; descriptor written to the descriptor FIFO.
       RAPIDS descriptor engine acks (tready) — injection latency target met.
```

Ordering: descriptors leave `descriptor_gen` in mailbox order; the CDC FIFO
and Delta preserve that order per stream, which is the ordering property
the formal inventory asserts (descriptor FIFO ordering, HAS §7).

Backpressure: if RAPIDS' descriptor FIFO fills, `tready` deasserts and the
CDC FIFO absorbs the stall; firmware sees `stall` only when the injection
queue itself fills (`MAX_INFLIGHT_DESCRIPTORS` outstanding) — a policy
signal to the scheduler, never a protocol error.

---

**Last Updated:** 2026-10-12
