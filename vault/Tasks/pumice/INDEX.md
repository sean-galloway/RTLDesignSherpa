# pumice — task rollup

DDR2/LPDDR2 memory controller (`projects/components/memory-controllers/pumice-ddr2-lpddr2/`).

| State | Count |
|---|---|
| [active](active.md) | 0 |
| [open](open.md) | 6 |
| [closed](closed.md) | 11 |
| [dropped](dropped.md) | 1 |

## Active

(none — the correctness backlog is empty. PUMICE-008 is marked ACTIVE in its
body but its own scope note says do NOT run it standalone, so it is counted
as open, not active. See the caveat under the shortlist.)

## Open shortlist

- **PUMICE-008** — adopt the external `axi4_intf_master_observer` and retire
  the harness's hand-rolled meters/hists (Sean 2026-08-26: no monitor/perf
  logic inside pumice; cheap interesting counters stay). GATES PUMICE-013 —
  until it lands the perf numbers carry the AMBA-HISTCH1 accounting error.
  **Conflicting guidance inside the task:** headed ACTIVE/"the DIRECTED
  path", but its scope note says "Not urgent. Do it when the pumice harness
  is next opened for other reasons, not as a standalone change — it touches
  the bridge map and the harness CSR readback, and pumice bitstreams are on
  the critical path." Resolve that before starting.
- **PUMICE-013** — characterize + tune the modes (the big one: sweeps in sim
  and on the board, recommended defaults per workload family). Wants 008
  first for the reason above.
- **PUMICE-014** — 15 of 17 files done. The 2 remaining are deliberate:
  `dfi_cmd_formatter_tb` needs its CHECK redesigned to be BFM-drivable (own
  task, not a mechanical port), and `wr_cmd_cam_tb` was DELETED 2026-08-28
  as dead code. Rule stands: no new test may hand-poke a valid/ready
  interface.
- **PUMICE-006** — mechanisms COMPLETE 2026-08-27, all three axes, every
  mode off by default and mutation-proven. Parked; reopens only if 013
  reports a gap.
- **PUMICE-CLEANUP** — doc placement + filelist consistency. P2 hygiene.
- **PUMICE-KMAP** — blocked on [[TOOLING-KMAP]], whose SCOPE CHANGED
  2026-08-28: the deliverable is now a three-part CONTRACT TABLE (term list
  -> invariants -> decision table), not a Gray grid. See
  [[signal-contracts-and-kmaps]]. Not startable from the pumice side until
  the emitter learns the new form.

## WARNING — task IDs 009-012 were REUSED

`closed.md` holds an ORIGINAL series (PUMICE-009 gearing, -010 addr-map
single knob, -011 LPDDR2 MR init, -012 LPDDR2 write-AP dropped writes). A
LATER series reused three of those numbers for unrelated work: "PUMICE-010"
(per-worker sim_builds), "PUMICE-011" (AMBA-HISTCH1 + multiid hist
accounting), and "PUMICE-012" (structure trackers). The later 010/011 were
never filed as their own entries and survive only as prose here and in
session memory.

So **a bare `[[PUMICE-010]]` / `[[PUMICE-011]]` link is ambiguous** — check
the date and subject before trusting it. The trackers task was renumbered to
**PUMICE-015** on 2026-08-28 and filed to closed.md; new tasks start at
PUMICE-016. Do not recycle an ID just because its task closed.

## Reading order for someone picking this up

The correctness backlog is EMPTY — PUMICE-001 closed 2026-08-25 (board
re-validated, matrix 65/70 data-clean, soak 0/15). Everything open is
cleanup or a gated feature. The July task cluster is fully resolved:
PUMICE-002 (stale hand-packed CSR write), PUMICE-003 (bank_lsb=0 striping,
fixed fcafc435), and PUMICE-004 (refresh collision, fixed 38c8ae63 with the
detector armed + mutation-proven 2026-08-24) all closed — the ledger had gone
stale against landed fixes FOUR times (002/003/004/007), so measure before debugging. PUMICE-006's
entry gate is now the PUMICE-001 board trip + a tiny-tREFI re-soak on the
08-16 bitstream.

Practice and rationale live in the [handbook](../../handbook/INDEX.md);
this directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.
