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
  axi5 `_cg` wrappers shipped this way (found in the axi45 docs scrub,
  fixed family-wide). `val/amba/test_mon_cg_gating.py` phase 2 asserts it.

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

- **Know your emission latency vs the minimum idle count.** Work that takes
  N cycles to become visible after its last covering term drops (e.g. the
  reporter presents a packet ~2-4 cycles after CAM-retire) can be stranded
  by an idle count < N: the clock stops before the pending flag rises, and
  the flag cannot wake what never asserted. Either document the minimum
  idle count (mon_cg docs say >= 4) or export a deeper busy signal that
  covers the pipeline (the reporter's `w_output_busy` is computed but not
  exported - the flagged full fix for TASK-070's residual).

- **Prove liveness by identity, not by count.** A delivery counter cannot
  tell one packet re-delivered N times from N distinct packets draining
  out of a FIFO. Phase 6 records packet VALUES and asserts no consecutive
  duplicates - that distinction is what turned "0 deliveries?!" into the
  discovery of both the sampling-skew test bug and the stranded-packet
  residual.

Related: [[reset-and-clocking]]. The wrappers: rtl/amba/{axi4,axi5,axil4}/
`*_mon_cg.sv`; the directed test: `val/amba/test_mon_cg_gating.py`.
