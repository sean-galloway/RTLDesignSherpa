---
title: Clock-gating activity terms
summary: Wake on peer VALIDs + ALL pending work incl. output-side packets; never peer READY; mask outputs with !gating for the wake-latency overlap.
---

# Clock-gating activity terms

An activity (wake) term must cover every place work can be pending, on both
sides of the block. Each rule below was paid for with a real bug in the
`*_mon_cg` monitor wrappers.

- **Peer VALID, never peer READY.** A consumer legitimately parks its
  response-ready high while idle; folding that READY into the activity term
  pins the block permanently awake and silently defeats gating. All 8 axi4/
  axi5 `_cg` wrappers shipped this way (found in the axi45 docs scrub).
  `val/amba/test_mon_cg_gating.py` phase 2 asserts it.

  **"Fixed family-wide" meant one family.** That sweep corrected axi4 and
  axi5 and stopped there. On 2026-09-02 the identical defect was still in ten
  more wrappers -- axil4 x4, axil5 x4, axis4 x2 -- found when qc round_33
  flagged ONE of them as SUSPECTED. A rule recorded here does not propagate
  itself: when a defect is a CLASS, grep every family for the pattern, not
  just the one the finding named. The command is three seconds:

      grep -hE "^\s*assign (user_valid|axi_valid)" rtl/amba/*/*_cg.sv | grep ready

  Three DOCUMENTS also still taught the wrong pattern
  (`amba_clock_gate_ctrl.md`, `clock_gated_variants.md`,
  `axis_clock_gating_guide.md`), one of them attributing it to a module that
  had already been corrected. Fixing RTL without sweeping the docs leaves the
  seed for the next wrapper someone writes.

- **Input-side valids and datapath busy are NOT the whole story: pending
  OUTPUT-side work must wake the block too.** The mon_cg wrappers gated on
  bus valids + core busy only; a monitor packet parked on `monbus_valid`
  behind a slow consumer froze when the clock stopped, and an ungated
  consumer holding ready high then accepted the SAME packet on every cycle
  (measured: 30 accepts of one packet in 30 cycles). TASK-070. Fix: the
  packet-pending flag is ORed into `user_valid`.

- **Mask outputs with `!gating` to cover the wake-latency overlap.** Gating
  can assert on the same edge pending work appears, and wake takes a cycle;
  during that overlap an output valid is frozen high but the gated domain
  cannot observe an accept. Masking the external valid with `!cg_gating`
  makes the consumer see nothing until the clock runs again. The mask only
  defers the valid's rise - it never truncates a visible valid, because once
  the pending-work term is high, gating cannot engage.

- **Cover the emission pipeline with an overlapping upstream term.** Work
  that takes N cycles to become visible after its last covering term drops
  (the reporter presents a packet ~2-4 cycles after CAM-retire) is stranded
  by any idle count < N: the clock stops before the pending flag rises, and
  the flag cannot wake what never asserted. The fix is a wake term that
  stays high THROUGH the pipeline until the output flag is up - here the
  monitor CAM's occupancy (`|active_transactions`): entries stay valid
  until their packet is marked into the reporter FIFO, and the registered
  count lags one cycle further, meeting `monbus_valid`. Prefer an existing
  status output that already brackets the window over exporting a new port
  (the `w_output_busy` export was flagged and turned out unnecessary).
  Note the terms are NOT mutually redundant: bypass packets
  (threshold/perf/debug) never come from CAM entries, so the output-valid
  term is still required alongside the occupancy term.

- **Prove liveness by identity, not by count.** A delivery counter cannot
  tell one packet re-delivered N times from N distinct packets draining
  out of a FIFO. Phase 6 records packet VALUES and asserts no consecutive
  duplicates - that distinction is what turned "0 deliveries?!" into the
  discovery of both the sampling-skew test bug and the stranded-packet
  residual.

Related: [[reset-and-clocking]]. The wrappers: rtl/amba/{axi4,axi5,axil4}/
`*_mon_cg.sv`; the directed test: `val/amba/test_mon_cg_gating.py`.
