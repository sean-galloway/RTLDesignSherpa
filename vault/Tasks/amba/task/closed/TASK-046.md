# TASK-046: monitor-lite output queues are gaxi_fifo_sync

**Priority:** P2
**Status:** closed 2026-10-16
**Owner:** sean galloway

Owner 2026-10-16: "monitor-lite output queue should be a gaxi_fifo_sync" (the
hand-rolled queues wrapped free-running pointers and needed a power-of-two
OUT_DEPTH; repo FIFOs take any depth).

## Done

- axi_monitor_lite, axi4ace_snoop_monitor_lite: one gaxi_fifo_sync, any
  OUT_DEPTH >= 2, gated on wr_ready only (in mux mode gaxi's count is
  combinational from the next-state pointers: gating on it is a loop).
- axis_monitor_lite, cxs_monitor_lite: two interleaved gaxi_fifo_sync banks
  (entry k -> bank k mod 2) so two writes a cycle still land in order; a
  registered occupancy count gates capacity to exactly OUT_DEPTH (any >= 1).
- Formal: axi_monitor_lite and axis_monitor_lite prove PASS + cover 7/7; the
  axis harness moved z3 -> bitwuzla (z3 >40 min on the new arrays, bitwuzla
  7 s). Flats regenerated; Makefiles carry the gaxi closure.
- Monitor-lite FULL 440/440; consumers GATE: rapids 510, stream, amber 200,
  bridge 183. misc axi4_intf_observer consumer_sustained/board_rate fail
  IDENTICALLY at clean HEAD (amba BUG-040), not caused by this change.
