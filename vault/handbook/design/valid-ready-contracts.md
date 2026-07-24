---
title: Valid/ready contracts
summary: Stability rules; observers gate commands only, never responses.
---

# Valid/ready contracts

- AXI stability: once valid asserts, it holds (payload stable) until ready.
  A COMBINATIONAL valid that can drop when an upstream condition changes is
  a protocol violation waiting for a stall to expose it. Case: the stream
  read engine's `m_axi_arvalid = grant && sched_rd_valid` can retract on
  abort paths (found by the K-map pass; the write side registers awvalid
  correctly). Register valids that cross an abort boundary.
- Ready may be combinational; never require ready-before-valid.
- Observer rule (owner design law): a monitor/observer may backpressure
  COMMAND channels only - responses/data must never be stalled. Monitors
  size so backpressure does not normally happen ([[sizing-invariants]]),
  but when it does, blocking must throttle-and-recover, never deadlock
  (the saturation-recovery contract, monitor_common_pkg::cmd_entry_reserve).
- Drain/pop strobes coupling two blocks deserve K-maps
  (bin/SIGNAL_CONTRACTS_KMAPS.md): the stream WLAST/drain term
  (`axi_wr_sram_drain = m_axi_wvalid && m_axi_wready`) fixed a real
  lost-WLAST deadlock.
