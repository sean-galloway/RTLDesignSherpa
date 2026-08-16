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
- **W must not lead AW on any bus carrying an AXI4 write monitor** (owner
  design law, 2026-08-14). AXI4 W beats have no WID, so a monitor attributes
  them by AW order: `axi_monitor_trans_mgr` pushes the AWID on the AW
  handshake and pops it on W-LAST. Same-cycle AW+W is supported (the queue's
  empty-push bypass takes the head straight off `cmd_id`); W strictly BEFORE
  its AW is not, and those beats are treated as strays because there is no
  AWID yet to attribute them to. Many commercial VIPs impose the same
  restriction. The alternative - deriving the target entry from a state
  predicate over the whole table - is what banking broke: the candidate set
  was not ID-matched, so the same-bank `pick_oldest` returned one winner per
  bank and one W beat advanced one transaction PER BANK
  ([[observers-do-not-drive]] is a different defect in the same family:
  both come from a monitor's bookkeeping being derived rather than recorded).
- Drain/pop strobes coupling two blocks deserve K-maps
  (bin/SIGNAL_CONTRACTS_KMAPS.md): the stream WLAST/drain term
  (`axi_wr_sram_drain = m_axi_wvalid && m_axi_wready`) fixed a real
  lost-WLAST deadlock.
- **Sideband sampled across a registered decision is a different beat than
  the one decided on.** When a decision registers (an arbiter's grant, a
  pipelined accept), any sideband consumed at COMPLETION time (a cost, a
  length, a tag) may already belong to the NEXT transaction - the consumer
  legitimately updates it the moment it observes the grant. Pipeline the
  sideband alongside the decision and consume the captured copy. *Case
  (2026-08-09): arbiter_deficit_round_robin debited the completion-cycle
  req_cost; a back-to-back client presenting its next frame's cost was
  debited the wrong frame. Caught by the TB's deficit mirror, fixed with a
  one-deep cost pipeline (r_cost_arb).*
