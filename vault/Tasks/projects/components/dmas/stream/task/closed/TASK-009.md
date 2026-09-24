# TASK-009: Signal contracts + K-maps for the significant STREAM signals (prove-by-construction)
> **Was `TASK-058` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Priority:** High
**Status:** [x] Done (2026-09-20) — closed by Sean. The optional formal
SVA of the stated invariants was NOT done; everything else the task asked
for is landed (036efde88). Original in-progress record follows.
**Was:** [~] In progress (2026-07-29) — the canonical workbook already existed
(`projects/components/dmas/stream/docs/gen_signal_contracts_kmaps.py` ->
`stream_signal_contracts.xlsx`); this session brought it CURRENT: added the
`w_addrgen_start` decider K-map (the TASK-059 fix) + `w_is_ext` contract, fixed
the citation drift my scheduler edit caused (24 `CITES` line refs) so
`verify_citations` is green again, and recorded the explicit placement rule in
the canonical note [[signal-contracts-and-kmaps]] (component `docs/`, one per
block, update-in-place — the gap that nearly caused a duplicate). Remaining: the
run-base-generator flush-on-start (invariant **I10** below) and optional formal
SVA of the stated invariants.

**Update 2026-09-20.** The citation gate was RED again (21 drifts, not caused by
this area's edits -- `scheduler.sv` moved +3 in `db672cd03`, `stream_core.sv`
+26 in `4aeaf3e63`, the monitor files up to +195 in `657d413c1`). Restored to
green; `CITES` is 73 -> 83. Four findings came out of doing it:

1. **The saturation-recovery contract documented the DEFECT as the contract.**
   Every row was stale: `cmd_entry_reserve` 2 -> **4**, `BLOCK_MARGIN` 1 -> **3**,
   `MAX_TRANSACTIONS` `+4`/68 -> `+MON_TRANS_MARGIN`/**72**, thresholds 67 -> 69.
   `axi_monitor_base.sv:679-690` states plainly that reserve=2 (margin 1) is the
   mechanism behind the observer tracking loss (4096 observed vs 3073 tracked) --
   so the workbook was publishing the broken sizing as correct. Corrected.
2. **`stream_core.sv` carried the same stale arithmetic** in comments ("+4
   covers in-flight skid/handshake overlap", "8ch default = 68"), orphaned by
   `baac9a77a` when MON_TRANS_MARGIN became 8. Corrected (comment-only;
   `stream_top_ch8` re-elaborates clean).
3. **"invariant I10" is a dangling reference.** There is no I-numbering anywhere
   in the generator -- invariants are free text in the "Key invariant" column.
   The numbered list the status line above promises was never written. Rather
   than invent an I10 to match the prose, the invariant is now recorded in the
   required form and numbered locally (I1-I3).
4. **86 source labels are structurally uncheckable.** `verify_citations` only
   validates `CITES` quoted snippets; the `f"{SCHED}:924-940"`-style labels are
   line RANGES, so drift in them is undetectable by design. Confirmed real, not
   theoretical: `SCHED:924-940` labels the read-prefetch map, but line 924 is now
   a comment and the expression sits at 927. Not fixed here -- making ranges
   checkable is tooling work ([[TOOLING-KMAP]] step 5), which [[TASK-001]] is
   already blocked on.

**Run-base generator: documented, deliberately NOT fixed in RTL.** The hazard is
confirmed and now bounded rather than vague: `u_rd_addr_gen`/`u_wr_addr_gen` take
`.rst_n(rst_n)` (SCHED:1029, :1051) -- the BLOCK reset -- so `r_channel_reset_active`
never reaches them (I1); `start` re-arms only the walker and never clears
`i_addr_fifo` (ADDRGEN:152) (I2); depth is 4 per direction (I3). So a channel
reset mid-generation strands up to **4 stale bases per direction**, and the next
descriptor generates behind them. Landed as a three-part CONTRACT TABLE (terms ->
invariants -> decision table) on the "K-maps scheduler" sheet. The decision table
has NO illegal row: all eight combinations are reachable, so nothing structurally
prevents the case -- it is bounded, not excluded.

RTL was left alone on purpose. The task's own text calls this "a good candidate
for the signal-contract treatment", the earlier `gaxi_drop_fifo_sync` `drop_all`
attempt regressed working cases and was reverted, and that attempt exists in no
branch, reflog or stash -- so it cannot be inspected and re-attempting it blind
would just reproduce the regression. Recorded hypothesis for whoever picks it up:
`gaxi_drop_fifo_sync` blocks normal read/write for the duration of a drop, which
is the likely "flush/read-timing interaction". Note the block is shared with
RAPIDS since `4aeaf3e63`, so an RTL flush has two consumers.

Also worth knowing: **no table in the workbook used the 2026-08-28 required form
until this one.** The handbook calls term-list -> invariants -> decision-table the
governing requirement; the existing sheets are all the older shape. Converting
them is [[TASK-001]] scope.

**Remaining:** only the explicitly-optional formal SVA of the stated invariants.
Everything the status line above listed as outstanding is now either done or
consciously deferred with a reason, so High priority may no longer be right.

**Goal:** Maintain explicit **signal contracts** and **Karnaugh maps** for the
significant control/handshake signals in STREAM — **especially in the read and
write engines** (`axi_read_engine.sv`, `axi_write_engine.sv`) and the scheduler /
descriptor-engine / SRAM-controller handshakes — so the design is provably
correct **by construction** rather than only by directed test.

**Why:** STREAM has already produced several *interaction* bugs that a per-signal
contract would have forbidden up front, not caught after the fact — the
WLAST/drain lost-beat deadlock, the SRAM drain double-count deadlock, and now
the extended chained-transpose corruption (TASK-059 / known_issues). Each was a
cross-block pipeline hazard: a signal asserted (or sampled) one cycle off, or a
shared config register aliased across descriptors. A written contract per signal
(producer, consumer, valid window, mutual-exclusion / one-hot invariants,
back-to-back and reset behaviour) plus a K-map for the combinational deciders
turns these into things that are wrong *on paper* before they ship.

**Scope (significant signals — at least):**
- Engine handshakes: `m_axi_*valid/ready`, `*last`, the SRAM `drain`/`valid`
  pair, per-channel `grant`/`req`, `w_active`/registered-valid gating.
- Scheduler FSM enters/exits and the write-completion timeout.
- Descriptor-engine prefetch + extended `chunk1` fetch (`w_want_ext`,
  `g_ext_fifo`) and the `stream_run_addr_gen` config-latch enables.
- Address generation stride/index/wrap deciders (K-map the mode selection:
  burst vs per-beat, wrap on/off).

**Deliverable:** a contract note per significant signal (table: producer /
consumers / valid window / invariants / reset) and K-maps for the combinational
deciders, landed under the STREAM docs tree (HAS/MAS or a dedicated
`signal_contracts/` area) and indexed. Cross-link each contract to the RTL line
and to any known_issue it would have prevented.

**Related follow-up (from TASK-059's fix):** the run-base generator
(`stream_run_addr_gen`) can still retain queued bases if an extended descriptor
is aborted mid-generation by channel reset (channel reset does not reach that
block). A flush-on-start (`gaxi_drop_fifo_sync` `drop_all`) would close it; a
first attempt regressed the working cases on a flush/read-timing interaction and
was reverted. Low-severity latent robustness item — a good candidate for the
signal-contract treatment.

---
