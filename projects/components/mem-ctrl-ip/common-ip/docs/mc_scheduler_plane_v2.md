# Scheduler Plane v2 — per-bank in-order core (family design)

Status: design, 2026-10-15; section 5 updated 2026-10-22 for the landed core. Owner direction: "the scheduler_plane in general
should work like this. Lets get the scheduler plane designed correctly and
validated." This document is the design record for the rework; MC-003 tracks
the work.

## 1. The architecture

The scheduler plane's DEFAULT core is per-bank in-order, LiteDRAM-class:

```
                 storage (per-bank in-order queues, one per direction)
                    |  per (dir, bank): head_valid, head_row, head_col,
                    v  head_id/len, queue_empty_behind_head
        +---------------------------+
        |  per-(dir,bank) head       |   each sequencer is INDEPENDENT:
        |  sequencers:               |   ACT -> columns -> AP-on-drain
        |   HEAD_ACT / HEAD_COL /    |   for its own bank's head entry
        |   HEAD_PRE                 |
        +------------+---------------+
                     | per-bank "head op ready" (advisory: registered
                     v  bank image + timers, LA where useful)
        +---------------------------+
        |  cross-bank arbitration mux|  round-robin bank rotor,
        |  (+ rd/wr preference +     |  1 command/cycle
        |   write-batching watermarks|  maintenance/refresh/init/ZQ
        |   + maintenance override)  |  override at top priority
        +------------+---------------+
                     |
        +---------------------------+
        |  shared output register +  |  THE JEDEC AUTHORITY (unchanged
        |  LIVE fire-stage re-check  |  pattern): bank_act/rdwr/pre_ready
        |  (hold-not-drop, bounded)  |  + global windows re-checked live;
                     |               |  a rejected pick is re-evaluated
                     v               |  next cycle, never executed
                  DFI cmd push
```

What makes this different from the current shared FR-FCFS pick core, and why
the mask-on-shared-pipe approach (commit 52829bbf3, reverted 7a7f80b00)
failed: the FR-FCFS core routes every pick through ONE 5-stage class
pipeline (classify -> 1a -> 1b -> pre-pick -> output). Restricting its
candidate mask to per-bank heads leaves at most one same-bank candidate, and
the successor head only appears when the predecessor FIRES -- single-bank
issue rate becomes pipeline-depth-bound (~4-5 cyc/col) instead of
tCCD-bound. The per-bank sequencers have no shared pipe: each bank's head
FSM advances on its own, the mux selects among ready banks each cycle, and
single-bank throughput is tCCD-bound.

## 2. Per-bank head sequencer semantics

Per (direction, bank), over that bank's in-order queue:

- HEAD_ACT: head exists && head.row != open_row && bank precharged/ready.
  Fires ACT(head.row). (The PRE below precedes it as needed.)
- HEAD_PRE: head exists && head.row != open_row && bank open (stale row)
  && tRAS + tRTP/tWR met. Because the queue is in-order, when the head's
  row differs from the open row, every older same-bank request has already
  issued -- the close decision is exact, no demand-wait, no heuristic.
- HEAD_COL: head.row == open_row && rdwr ready && tCCD/tWTR/tRTW gates.
  Each head entry carries its beat count; the LAST beat of the head, when
  the queue behind it is EMPTY, issues as RDA/WRA (CLOSE_ON_DRAIN -- per
  this core it is queue-empty, exact, replacing the FR-FCFS
  youngest-same-row heuristic). Otherwise RD/WR.

Order within a bank is arrival order by construction. Across banks the mux
picks one ready bank per cycle (round-robin; write-batching watermarks and
direction preference layered on top as today).

## 3. JEDEC authority (unchanged contract)

Bank timers (mc_bank_timers), global timers (tCCD/tWTR/tRTW/tFAW/tRRD), and
the fire-stage live re-check carry over verbatim from the current core: the
sequencers advise from the registered image; the output register re-checks
the LIVE safe_* before anything leaves; holds (not drops) for
timer-in-flight ACTs/PREs with bounded waits; maintenance (training/ZQ),
refresh (incl. per-bank drain PREs -- natural in this model: the drain IS a
per-bank PRE sequence), and init command injection keep their override
priority and all-banks-idle gates.

## 4. Storage seam (per-bank in-order queues)

The plane consumes a per-bank head interface instead of the N-wide
CAM-shaped vectors:

- storage -> sched, per (dir, bank): head_valid, head_row, head_col,
  head_id/len/etc, behind_empty (no younger entry in this bank's queue).
- sched -> storage: head pop / commit strobes (fire-qualified), per bank.

Granite entry store: allocation becomes per-bank physical queues
(depth 2/bank, total 16 at 8 banks; A7 already runs NUM_ENTRIES=16). The
wr-data fill path lands beats by (bank, slot) exactly as today; BRAM data
path unchanged.

Pumice storage plane: keeps the research core (FRFCFS) for now; its
migration to the per-bank seam is a separate step (its rd_cmd_cam already
exposes oldest-entry ports -- the per-bank heads can be derived without new
storage).

The AGENTS.md storage-backend co-verification rule applies per backend at
max depth with >N chunks in flight.

## 5. Modes and the research core

Plane param `SCHED_CORE` (int, `mc_common_pkg`): `MC_SCHED_BANK_PICK` (1,
the default and the family design: `mc_bank_pick` on the per-bank head
records, landed 2026-10-22 as mem-ctrl recovery Phase 2) or
`MC_SCHED_FRFCFS` (0: `mc_cmd_arbiter` on the per-entry vectors).
`mc_cmd_arbiter` remains the research core for pumice's window/ordering
studies (order modes, row/col selectors, access preference, QoS) and for A/B
characterization; it is selected, not replaced. The earlier `BANK_FIFO`
parameter and its core `mc_bank_sched` (the 2026-10-15 skid-seat design that
read the store's live head views, MC-003) are retired; the `BANK_IN_ORDER`
pick-mask plumbing in `mc_cmd_arbiter` (52829bbf3) is gone with them.

What the landed core looks like, against sections 1-3 above: the per-(dir,
bank) "head sequencers" are a one-cycle decode over the REGISTERED records
(`mc_head_rec_t`, [[plane-boundary-registered-snapshots]]) rather than
skids over a live view; the cross-bank mux is a registered round-robin with
aging and class-alternation overlays; the fire stage is unchanged in
contract (live JEDEC re-check, hold on a closed timer). Two additions were
needed to land dependent hops on the JEDEC floor through a two-stage pipe:
a one-cycle pop shadow (the record lags a pop by a cycle; the fired pair is
served from its second record) and a next-op hint (a fire tells the arbiter
what the same pair wants next, bypassing the register when the hop is
shorter than the pipe). Read the header of
`common-ip/rtl/fub/mc_bank_pick.sv` for the mechanism; the plan
`docs/superpowers/plans/2026-10-21-mem-ctrl-recovery.md` section 2.2 for the
reasoning.

## 6. Validation plan

1. Common-ip macro: new store<->per-bank-sched contract test at NUM_ENTRIES=16,
   >16 chunks/direction, commit/drain/B/issue completion (AGENTS.md rule).
2. Granite dv: geared suite (incl. gate-8-12 at depth 16), core, uart smoke
   at board geometry.
3. Directed stream checks: test_pumice_close_drain equivalents for the
   per-bank core (group drain -> exactly one AP close; steady col_major at
   the 13-cycle floor; zero explicit PREs).
4. Pumice regression on FRFCFS (unchanged path).
5. A7 board: all 14 scenarios on granite (expect row_major >= 570 held,
   col_ilv >= 354 held or better, col_major toward the 369 floor, 14/14
   integrity), pumice spot-check unchanged.
6. Whole-harness lint incl. decl-order.
