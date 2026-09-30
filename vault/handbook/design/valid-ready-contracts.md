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
- **A "reject" that does not gate `valid` rejects nothing** (owner design law,
  2026-09-27, pumice BUG-003). When a block re-checks safety at its output
  register and has BOTH an internal "this really issued" strobe and an external
  `valid`, the safety term must appear in **both** or the block lies to itself.
  pumice's arbiter had

        assign w_out_safe   = (r_do_rd || r_do_wr) ? bank_rdwr_ready_i[...] : ...;
        assign w_out_reject = r_pick_valid && !w_out_safe;   // frees the slot
        assign w_fire_out   = r_pick_valid && cmd_ready_i && w_out_safe;
        assign cmd_valid_o  = r_pick_valid;                  // <-- no safe term

  and a comment asserting "Dropping is lossless". Freeing the output register
  is not dropping: while the rejected pick sat there, `cmd_valid_o && ready`
  was true, the FIFO took it, and the DRAM executed it. Meanwhile `w_fire_out`
  — which gates `evt_*` to the bank timers, the post-fire guard shifts, AND the
  CAM retire — stayed low, so the controller's model recorded the command as
  never issued. **Two consequences, and the second is the one that bites:** the
  DRAM got an illegal command, and because the CAM entry was never retired the
  same read was issued AGAIN after the re-pick. One AXI read, two RD commands
  on the bus, one extra read return. It was chased for weeks as a DV
  read-return modelling defect and then as a missing precharge guard; it was
  one missing `&& w_out_safe`.
  **The test:** for any output-register safety gate, write down the set of
  consumers of the safety term. If `valid` is not in that set, the design
  issues commands it has decided not to issue. Make the fire and the push the
  same expression (`w_fire_out == cmd_valid_o && cmd_ready_i`) so they cannot
  diverge again. Retracting `valid` this way is safe against a `gaxi_fifo_sync`
  (its `wr_ready` is a registered `!r_wr_full`, so no loop, and it pushes only
  on `wr_valid && wr_ready`) — but it IS a valid retraction, so check the
  consumer, per the AXI stability rule above.
- **Instrument the port, never re-derive the condition.** The trace that found
  this originally reconstructed the push as `r_pick_valid && cmd_ready_i`
  because that is what `cmd_valid_o` was assigned to. After the fix that
  instrument still reported 9 pushes the DUT no longer made. A probe that
  re-derives a DUT expression measures the design it was written against;
  read `cmd_valid_o` itself.
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
- **gaxi FIFOs in rtl/ are mux-read (`REGISTERED=0`) unless there is a
  stated reason; registered read is the exception (Sean, 2026-09-09).**
  Registered read moves the data a clock after the handshake and every
  consumer has to know it. Details: `gaxi_fifo_sync` with `REGISTERED=1` loads its output
  register from the current read pointer, so `rd_data` lags a pop by one
  clock; the BFM calls this `fifo_flop` mode and captures data one cycle
  after `rd_valid && rd_ready`. A consumer that builds its output from
  `rd_data` in the handshake clock sees the popped entry AGAIN on the next
  clock of a back-to-back read and never sees the one after it: one packet
  duplicated, one lost, no counter moving. Use `REGISTERED=0` (mux read,
  data valid in the handshake clock) when the data is consumed
  combinationally, or capture `rd_data` the clock after. *Case
  (2026-09-09): wb4_monitor's first test, with the event FIFO wired exactly
  like apb4_monitor's, wrote completion / timeout / completion on three
  consecutive clocks and emitted completion, the same completion, timeout.
  apb4_monitor, apb5_monitor and axi_monitor_reporter shared the wiring
  and were switched to mux mode on 2026-09-10, each with a directed
  three-events-on-consecutive-clocks witness (TASK-086, closed).*
- **A response channel with no ready forces the REQUESTER to reserve space
  before it launches.** If a protocol's completion cannot be back-pressured
  -- Wishbone terminates with ACK/ERR/RTY and the master has no way to stall
  them -- then "issue now, find room later" has no safe failure mode: the
  answer arrives and either overwrites something or is dropped, silently, with
  no counter moving. Gate issue on a reserved slot instead. *`wb4_master`
  issues only while `r_reserved < RSP_DEPTH`, so `RSP_DEPTH` bounds both the
  queue and the transfers on the bus; `wb4_slave` does the mirror with
  `MAX_OUTSTANDING`. Ten modules in `rtl/` now hand-roll this counter, which is
  an argument for a shared credit-gated skid.*
- **Merging independent response channels into an in-order protocol needs a
  side queue, not a mux.** AXI4-Lite's B and R are independent and a slave may
  answer them in any order; Wishbone B4 terminates in issue order. Passing
  each response straight through therefore breaks the ordering rule the moment
  a read finishes behind a slow write, which is routine. Record each command's
  direction in an in-order queue at issue and release only the head. *Case
  (2026-09-10): `wb4_to_axil4_core`. The cost is head-of-line waiting, so its
  `OUTSTANDING` defaults to 1 and serialises; the opposite direction
  (`axil4_to_wb4_core`) gets the same ordering free, because merging INTO an
  in-order protocol is the easy way round.*
- **Gate a producer's READY on an extra condition and you must gate the VALID
  every consumer sees, too.** A handshake completes where `valid && ready`
  meet, and each consumer evaluates that for itself. If a tap is added that
  holds the producer back -- a comparator FIFO, an observer, a second
  consumer -- while the original consumer still sees `valid` high and drives
  its own `ready`, that consumer completes a transfer the producer never
  retired. The producer then re-presents the same beat and the consumer takes
  it AGAIN. *Case (2026-09-30, `rs_loop_harness`): a comparator was added to
  check two RS decoders against each other, its FIFO write ready folded into
  `dec_out_ready` but not into `chk_tvalid`. Beats duplicated on whichever
  side the comparator stalled: the checker counted 6 packets for 4 blocks with
  a data error and a bad CRC, while the comparator simultaneously reported the
  very same stream as beat-perfect -- because the comparator saw the retired
  beats and the checker saw the duplicated ones. The two symptoms disagreeing
  is the tell.*
- **A monitoring tap that cannot back-pressure will drop, and dropping makes
  its own verdict a lie.** The first version of that comparator wrote its two
  FIFOs with `wr_valid = valid && ready` and discarded `wr_ready` into an
  unused-signal sweep. With both consumers drained at the same rate the two
  FIFOs stayed in lockstep and it worked for the whole bring-up; the moment
  the two drain rates were randomized INDEPENDENTLY, one FIFO overflowed,
  beats were dropped, and the comparator began pairing beat N of one stream
  with beat N+k of the other -- reporting ~690 of 700 beats as mismatching
  between two decoders that agreed completely. Either honour the ready, or
  carry a sticky flag that invalidates the verdict; silently discarding
  `wr_ready` in an `unused` XOR is how the hole gets made. Prefer both: the
  flag is what stops a future regression being read as a data bug.

Related: [[streaming-no-fsm]], [[no-assertions-in-rtl]], [[randomization]].

