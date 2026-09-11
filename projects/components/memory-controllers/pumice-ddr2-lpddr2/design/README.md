# pumice ideal scheduler / datapath — spec-first design

**Status:** design spec (2026-09-07). This directory defines the *ideal* command
and data-path signalling **before** the RTL, so the rewrite targets a spec rather
than patching the current design. Two kinds of artifact:

- Truth tables for the control logic live in the ONE signal-contract workbook,
  `../docs/pumice_signal_contracts.xlsx` (generator:
  `../docs/gen_pumice_signal_contracts.py`). The `kmaps/` directory and its
  three separate workbooks were merged into it on 2026-09-10 -- four workbooks
  across two directories with overlapping content and no way to tell which was
  current.
- `waves/` — WaveJSON timing diagrams (`gen_waves.py`) for the ideal cadence.
  Render at <https://wavedrom.com/editor.html> or `npx wavedrom-cli -i f.json -s f.svg`.

Regenerate: `python3 ../docs/gen_pumice_signal_contracts.py && python3 gen_waves.py \
&& python3 gen_write_path.py`.

DDR2-300 @ aclk 75 MHz, DFI_RATE=2, BL4. Peak = **600 MB/s** (8 B/cycle).

**STATUS 2026-09-10 -- the gap this spec was written to close is CLOSED.** Pumice
measures **570.3 MB/s write / 571.3 MB/s read**, both ~95 % of peak, 14/14
characterization points integrity-clean, 219 regression tests green. Under
concurrent read+write in one window it sustains 570.1 MB/s total, **2.00x
LiteDRAM** (285.6) through the identical harness.

Everything below was written on 2026-09-07, mid-campaign, when pumice sat at
~15 % of peak and the write path wedged. **It is phrased in that moment's present
tense** -- "today", "the wedge", "the current failure chain" -- and eleven RTL
commits landed afterwards and closed those failures. Read it as the spec it is,
plus a record of what the failures were, not as a description of the controller
you have now. The dated `RTL STATUS 2026-09-10` lines in
`../docs/pumice_signal_contracts.xlsx` say which items are genuinely still open
(two, neither costing measurable bandwidth).

---

## Why the current scheduler only reaches 15 %

The measured wall is exact: one column access moves 8 B = **one** cycle of DFI
data, but the scheduler issues a column every **~6.7 cycles** → ~85 % of the bus
is idle. The pick pipeline is **not** the cause (a real pipeline is latency, not
throughput — see `waves/07_pick_pipeline_ideal.json`). Two things cause it:

1. The column mask term **`!w_col_inflight_bank`** (`pumice_cmd_arbiter.sv:361-363`,
   applied 513-516/528-531) forbids a second same-bank column from even being
   *classified* while the first is anywhere in the 3-flop pick pipeline → 1
   same-bank column per ~pipeline-depth instead of per **tCCD**. Every other
   gate in that mask is a real DRAM timer (`tccd_ok_i`, `bank_rdwr_ready_i`, …);
   this one is pick-pipeline occupancy, not a DRAM constraint.
2. Per-bank serialization only helps *cross*-bank workloads; the single-stream
   char is ~one active bank at a time, so it stays at the same-bank rate.

## Why the mask can't just be deleted — the real root cause

Removing it (the reverted per-entry mask) **deadlocks** under real read latency.
Root-cause (full evidence in the analysis; key file:line below):

- The arbiter picks against a **registered, 1–3 cycle STALE** bank image
  (`pumice_cmd_arbiter.sv:454-468`; timers add a stage, `bank_timer.sv:90-129`).
  `!w_col_inflight_bank` is the *only* interlock stopping a same-bank column from
  being classified against that stale image. Relax it and the 2nd same-bank
  column can issue while the bank is mid-transition (row closing on PRE/AP/refresh,
  or tRCD not yet reflected) → a **read lands on the wrong/closed row and never
  returns valid data**.
- That read wedges the **strictly in-order AR-order read reorder buffer forever**
  (`pumice_rd_cmd_cam.sv:366-420`: drain gated on the *oldest* entry's
  `r_ready`; a younger ready entry can never pass a stuck older one). The return
  fill is **positional, untagged** (`pumice_rd_cmd_cam.sv:237-269`,
  `pumice_dfi_rd_aligner.sv:112-136`) — one short/dropped burst desyncs every
  later read with no recovery.
- Reads and writes share **one in-order DFI command FIFO**
  (`pumice_mem_cmd_scheduler.sv:505-519`); a stalled RD at its head
  **head-of-line-blocks the queued WRs** (`pumice_dfi_cmd_path.sv:130-148`), the
  write drain stalls (`pumice_wr_data_cam.sv:486-504`), and `commit_done`/B
  never fire (`:583-585`). **That is why the write engine wedges "first"** — it's
  the first observable, not the root.

So the 15 % ceiling and the deadlock are the **same defect** seen two ways: the
arbiter reasons about bank state that is stale, so it must serialize same-bank
columns to stay safe, and the return/command paths can't recover if it doesn't.

---

## The ideal spec (what the RTL must do)

Three coupled changes, specified by the artifacts here:

1. **Forward-state classification** — classify a same-bank column against the
   *post-in-flight-op* bank state, not the registered-stale image. The arbiter
   already tracks the in-flight op (`r_bank`, `w_inflight_col`,
   `w_col_inflight_guard`); OR its pending row-open/close + tCCD/turnaround
   effect into the column mask. Then same-bank columns pipeline at **tCCD** with
   no stale-image race, and `!w_col_inflight_bank` is deleted.
   → `pumice_signal_contracts.xlsx` (CMD_DECISION, FORWARD_STATE),
     `waves/07`, `waves/08`.
2. **Tag-based, recoverable returns** — match DFI returns to reads by slot/id,
   not issue-FIFO position; add a per-read length watchdog so a short/lost burst
   can't wedge the AR-order drain. Return depth D ≥ ⌈(t_rddata_en+CL)/tCCD⌉ = 5,
   so the pipe stays full across the read round-trip.
   → `pumice_signal_contracts.xlsx` (RD_RETURN, RETURN_TAGGING),
     `waves/01`, `waves/08`.
3. **Decouple read/write issue** — split the DFI command FIFO into read/write
   lanes (or let a WR bypass a RD stalled only on `rd_op_ready_i`), so a read
   stall can never be reported as a write wedge.
   → `pumice_signal_contracts.xlsx` (CMD_DECISION notes), `waves/09`.

Target: same-bank open-page streaming at **~tCCD rate** (waves/01, waves/02),
cross-bank ACT pipelining (waves/04), i.e. ~500–600 MB/s.

## Artifact index

| file | defines |
|------|---------|
| `pumice_signal_contracts.xlsx` sheets `CMD_DECISION` / `AP_DECISION` / `TIMING_GATES` / `FORWARD_STATE` | FR-FCFS command decision, AP/page-policy, timing-gate legend, forward-state |
| `pumice_signal_contracts.xlsx` sheets `WR_DRAIN` / `WR_COMMIT_B` / `RD_RETURN` / `SAME_BANK_OUTSTANDING` / `RETURN_TAGGING` | wr drain, B-gating, rd return, per-bank outstanding tracker, return tagging |
| `waves/01_open_read_stream` | ideal RD stream @ tCCD — the throughput target |
| `waves/02_open_write_stream` | ideal WR stream @ tCCD |
| `waves/03_page_miss_act_rd` | ACT→tRCD→RD first-access latency |
| `waves/04_bank_parallel_act` | cross-bank ACT pipelining (tRRD/tFAW) |
| `waves/05_page_conflict_pre_act_rd` | PRE→tRP→ACT→tRCD→RD |
| `waves/06_refresh_insertion` | PREA→REF→tRFC→resume |
| `waves/07_pick_pipeline_ideal` | pipeline = latency, not rate (the correction) |
| `waves/08_same_bank_outstanding_fix` | ≥2 same-bank columns in flight, forward-state + tagged return |
| `waves/09_failure_stale_image_wedge` | the failure chain this design CLOSED (historical reference: what NOT to do) |
| `pumice_signal_contracts.xlsx` sheets `DRAIN_HANDSHAKE` / `CM_RD_STALL_CANDIDATES` / `SERIALIZER_OWED` / `B_CONSOLIDATION` | **write drain/commit detail**: DRAIN_HANDSHAKE, CM_RD_STALL_CANDIDATES (why the DFI stops accepting writes -- the same-bank-WR wedge), SERIALIZER_OWED, B_CONSOLIDATION |
| `waves/10_write_drain_pipeline_ideal` | ideal write drain (2 same-bank WR pipelined, no stall) |
| `waves/11_write_same_bank_wedge_ref` | the write-path wedge this design CLOSED (historical reference; drain FIFO fills, commit_ready drops) |
| `waves/12_rd_return_ring` | reads in flight beyond the scheduling window (ticket ring) |
| **BAD PERF -- correct, just slow** | *what a healthy-looking but underperforming capture looks like* |
| `waves/13_bad_admit_gate_half_rate` | the AR admit gate at half rate: one sub-command every two cycles, 291.7 MB/s against a 570 write, integrity perfect (PUMICE-025, fixed) |
| `waves/14_bad_ring_depth_bound` | reads bounded by RD_RET_DEPTH/round-trip rather than tCCD: 32/49 = 0.78 col/cyc = 470.9 MB/s |
| `waves/15_bad_page_thrash_col_major` | PRE+tRP+ACT+tRCD per column: 102.4 MB/s against 571.3 for row_major |
| `waves/16_bad_rw_turnaround_thrash` | tWTR/tRTW paid on every direction switch -- the workload the reorder window exists for |
| `waves/17_bad_refresh_storm` | PREA+REF+tRFC eating the bus, and every open row closed behind it |
| **PATHOLOGICAL** | *shapes that mean something is wrong* |
| `waves/18_patho_row_pingpong_masters` | two masters on different ROWS of the same banks: PRE+ACT between every column (collapsed row_major 570 -> 224 MB/s) |
| `waves/19_patho_inorder_serialization` | in_order: only the CAM head may issue, so page hits sit behind a miss (~17x) |


## Correction (2026-09-07): the wedge is in the WRITE PATH, not the arbiter

Four fixes targeting the arbiter -- including the full correct-by-construction
shadow bank-state (the signal-contract workbook's FORWARD_STATE sheet) -- all wedge IDENTICALLY at
`gen_wr_done` in the WRITE-ONLY phase. A fundamental arbiter redesign failing the
same way proves the wedge is downstream: the **write drain/commit path** when
same-bank WR columns pipeline. The write-path sheets above (`DRAIN_HANDSHAKE` ... `B_CONSOLIDATION`
+ waves 10/11) defines the ideal drain/commit signalling and scopes the fix to
the CM_RD_STALL candidates. The shadow arbiter is sound and kept for reuse once
the write path accepts the concurrency; it is not this bug.

## Measurement (2026-09-07): on-silicon ILA confirms command-issue starvation

An ILA on the DFI boundary + internal probes (`w_cmd_v`/`w_cmd_rdy`/`w_cmd_op`,
`w_dfi_wrdata_en`, `w_dfi_rddata_valid`, `r_outstanding` in the rd aligner)
captured a sustained `open_interleave` stream (OPEN page + BANK_INTERLEAVE),
4096 aclk samples at 75 MHz. This is the direct measurement the spec above was
reasoning toward, and it **confirms the diagnosis and rules out two alternatives.**

| metric | WRITE stream | READ stream |
|--------|--------------|-------------|
| `w_cmd_rdy` (DFI ready to accept a cmd) | **100 %** | **100 %** |
| `w_cmd_v` (arbiter offering a cmd)      | 33.2 % | **3.2 %** |
| `v & !rdy` (arbiter offers, DFI stalls) | **0 %** | **0 %** |
| arbiter idle (`v == 0`)                 | 66.8 % | 96.8 % |
| `wrdata_en` phase-duty                  | 32 % (~220 MB/s, matches board) | -- |
| `rddata_valid` phase-duty               | -- | 2.4 % |
| `r_outstanding`                         | 0 | **max 6, mean 0.37** |

**The DFI never backpressures** (`w_cmd_rdy` pinned at 100 % both directions):
the controller is not blocked downstream. The arbiter simply has nothing to
offer -- 2/3 of cycles on writes, 97 % on reads.

The write window around a stall is unambiguous: the arbiter fires ~3 WR columns
back-to-back (`gap = 1`), then **goes idle ~9 cycles while the current burst's
write data drains to the DFI** (`wrdata_en` active, banks stepping 2->6), then
resumes. Column-fire gaps: 1054x 1-cycle vs **259x 9-cycle bubbles** -- roughly
half the window wasted, entirely in inter-transaction idle, with the page open
(only 24 ACT / 16 PRE in 4096 cycles).

Two hypotheses are **falsified by silicon**:

- Reads are **not** CAM-depth-limited. `r_outstanding` peaks at 6 and sits at 0
  for 89 % of samples -- deepening the 8-entry `rd_cmd_cam` would change nothing.
  Reads are starved at *issue*, not blocked at *retire*.
- The write path is **not** downstream-backpressured here. `w_cmd_rdy` is 100 %;
  the earlier "write wedge" is the same-bank-pipelining case, not this one.

So the wr>500 / read-symmetry fix is to **decouple command issue from data
drain / read round-trip**: keep the next transaction's columns flowing while the
current burst drains, lifting `w_cmd_v` duty from 33 %/3 % toward the 100 % the
DFI already offers. That is the upstream production path (intake -> splitter ->
CAM -> scheduler), matching `SERIALIZER_OWED` / `DRAIN_HANDSHAKE` in
`pumice_signal_contracts.xlsx` -- not the arbiter column mask and not the CAM depth.

Instrumentation: `mark_debug` on the probes above + `make bitstream-ila`;
capture via `fpga/tcl/capture_ila.tcl` (trig `wr`/`rd`) driven by a sustained
`open_interleave` stream. Raw CSVs decoded with the per-cycle histogrammer.

### Related pre-existing failure (deferred to the wr>500 work)

`test_ddr2_char_uart_smoke_rate2_strict` (framework dv) fails `rd=False, mism=8`
at `cmd_delay=0` -- and fails **byte-for-byte identically on pristine HEAD**
(verified in a detached worktree), so it is pre-existing, NOT introduced by the
framework relocation or the bridge regen. It was purpose-built to catch this
(commit 58873c8d "strict write-timing regression that reproduces the board
bug"); its own comment predicts the mode: a one-beat write-stream rotation ->
the LFSR seed lands at the last column -> `mism`. This is very likely the SAME
write-path weakness the ILA measured above (command issue serialized behind
write-data drain). Chase both together when resuming wr>500.

## Fix analysis (2026-09-08): the write-BW ceiling, root cause + options

Follow-up to the ILA measurement. Deep read-only trace of the write path pins
the ~37% write ceiling to the arbiter keeping too few columns in flight, not to
any downstream backpressure (DFI `w_cmd_rdy`=100%). At aclk=75, 600 MB/s = 8
B/cycle = **1 column/cycle**; the DFI (150 MHz) can absorb that, so the wall is
purely arbiter issue duty (33% wr / 3% rd). Two independent mechanisms:

**Gate 1 — arbiter same-bank pick guard (`pumice_cmd_arbiter.sv:529`).**
`!w_col_inflight_bank[wb]` is applied UNCONDITIONALLY in the column mask, but the
comment (`:350-360`) says it is an auto-precharge-only span meant to be gated by
`f_ap(b)`, and the per-entry replacement (`w_wr_col_inflight_ent`, `:339-349`) is
**dead code** (computed, never referenced). It caps SAME-bank column issue to
~1/3 cycles (the pick-pipeline depth) instead of 1/tCCD. RISK: relaxing it is the
reverted deadlock (a 2nd same-bank column issuing against the 1-3 cycle STALE
bank image → read on a wrong/closed row). The bank-transition guards
(`r_ap_closing`, `w_pre_col_guard`, `w_preact_bank_guard`) are SEPARATE terms, so
the safe form is per-entry double-issue + tCCD for stable-open rows — but the
prior attempt shows this needs care. Only helps SAME-bank streaming; the board's
`open_interleave` ROTATES banks, so this is not the board's dominant limiter.

**Gate 2 — wr-data CAM slot-recycle latency (`pumice_wr_data_cam.sv`).** WR issue
is gated on `wr_commit_ready_i` = room in `u_drain_q` (`:494`, DEPTH=NUM_ENTRIES=8)
AND on schedulability `sch_valid = r_valid && r_fdone && !r_sched` (`:450`), which
needs a filled entry. The SRAM slot + entry free at drain-CONSUMER-last
(`w_cm_fire && w_hd_blast`, `:714-719`), where `w_cm_fire` = the write-data CDC
FIFO accept (`pumice_core.sv:538-539`). The drain-FIFO already pops at
FETCH-last (`:577`); the entry lives ~1 skid + CDC-accept longer. Under the
rotating board workload the arbiter empties its handful of ready entries, then
stalls waiting for the late free → the "3-4 then 9" cadence. FIX B: free the
entry/SRAM at fetch-last (mirror the `:577` pop). SAFETY GATE (unresolved
read-only): the snarf serves only `!r_sched` writes (`:312-320`) — a scheduled
write is not forwarded, so a same-id read after it must be ORDERED on the write's
completion. Whether that ordering waits on B (`commit_done`, which Fix B leaves
at consume-last → SAFE) or on the CAM entry's presence (→ HAZARD if evicted
early) is the one thing that decides Fix B's safety, and it needs a targeted
RAW test to settle before implementing.

Not a safe lever: bumping NUM_ENTRIES (shared rd+wr, age matrix is N², board is
near-critical on timing) — and it likely does not help, since the arbiter uses
only ~2.7 of 8 entries today (the problem is keeping entries in flight, not the
count).

Reads (#3) are the same class: starved at ISSUE (w_cmd_v=3%, r_outstanding≤6, CAM
never fills), not CAM-limited — the read-column issue rate, mirror of Gate 1/2.

Validation: the core perf ceiling tests measure the AXI-W side (100%), NOT the
DFI-drain duty, so they do NOT reproduce the board bubble. The real vehicle is
the board char/page_policy sequences (`run_smoke.py --sequences init char`).

### Fix B experiment result (2026-09-08): NULL — slot-recycle is not the limiter

Implemented Fix B (free the wr-CAM entry/SRAM at drain fetch-last instead of
consumer-last) and board-validated it with a rigorous before/after on the SAME
measurement (pumice_char.measure, open_interleave = OPEN + BANK_INTERLEAVE, bl16,
incremental, txn 4000):

  baseline (no Fix B):  wr 293.0  rd 179.9 MB/s  mism 0
  with Fix B:           wr 293.0  rd 179.8 MB/s  mism 0

**Identical.** Fix B is data-correct (waw/b2b/core_dfi pass), timing-met (WNS
+0.127 vs baseline +0.025), and regression-free (the paging_sched_cross
static_close failure is pre-existing at HEAD, not caused by Fix B) — but it moves
the write BW by 0. The slot-recycle latency was NOT the write-BW limiter.
Reverted.

Two things this exposes that must be reconciled before the next attempt:
1. **The char timer-BW (293 = 49% of peak) disagrees with the ILA wrdata_en duty
   (~32% ~ 220).** Same config, different number. One of them is not measuring
   the sustained DFI write duty. Resolve this first — the fix target depends on
   which is right. The char measures beats/timer-window; the ILA measured
   wrdata_en high/total over a 4096-cycle window. If the char window excludes the
   inter-transaction gaps (measures only the active phase), 293 overstates
   sustained BW and the real ceiling is nearer 220.
2. The remaining gap to 500 is NOT the two gates identified (Gate 1 same-bank is
   deadlock-risky + irrelevant to rotating traffic; Gate 2 slot-recycle is this
   null result). The next diagnostic should re-capture the ILA under THIS exact
   char workload and instrument which of {wr_commit_ready, sch_valid, the bank
   timers, refresh} de-asserts during the arbiter-idle window — the read-only
   trace could not disambiguate without the running waveform.

### Forward-state fix attempt (2026-09-08): DIRECTION CONFIRMED, needs the full overlay

Implemented the wave-07 fix (bypass the per-bank occupancy mask w_col_inflight_bank
for open-page columns, gated by f_ap) on both rd/wr column masks:

  test_pumice_arbiter_issue_rate: rate = **1.0000** (200 fires / 200 cycles)

That is EXACTLY wave 07's "ONE command PER CYCLE" — up from ~0.5. The pipeline-
throughput cap IS the occupancy mask, and removing it hits the ideal. Confirmed.

BUT the naive gate DEADLOCKS the core_dfi write-readback (hangs). The occupancy
mask does two jobs; f_ap-gating only covers the first:
  1. AUTO-PRECHARGE same-bank serialization (bank closes on RDA/WRA) -- f_ap covers.
  2. tRCD / stale-image bridging: the bank rd/wr-ready + tCCD timers are REGISTERED
     and lag an in-flight ACT/column by 1-3 cycles, so a same-bank column issued
     against the stale image lands on a not-yet-open / wrong row -> the read never
     returns -> AR-order drain wedges. This is the reverted-deadlock mechanism.

So the complete fix is wave 08's FORWARD-STATE overlay, not a one-liner: track,
per bank, the in-flight ACT/column so the column classify uses the FORWARDED
tRCD/tCCD (post-in-flight-op state) instead of the registered-stale image; add
the per-bank outstanding counter (D = ceil((t_rddata_en+CL)/tCCD) = 5 for reads,
bounded by the aligner/rd-cmd-cam return depth) to replace the occupancy mask.
Then w_col_inflight_bank deletes safely and columns pipeline at tCCD (1/cycle
aggregate across banks) -> the path to 500+. This is a focused arbiter+timers
change (the signal-contract workbook's FORWARD_STATE sheet, waves 07/08), timing-critical, board-validated.

### FUB-by-FUB scrub (2026-09-08): the write-path bug peeled to 3 layers

Disciplined per-FUB verification against the waves (baby steps):

- **pumice_wr_data_cam vs wave 10**: MATCHES. Added a wave-10 scenario to the
  FUB test (commit N same-bank bursts, DFI accepting) -> drained=8/8,
  commit_ready never drops, one B/burst. The drain is NOT the wedge.
- **pumice_dfi_wr_serializer vs wave 02/10**: MATCHES (existing bubble-free +
  tccd_paced tests). The serializer streams; not the wedge in isolation.

That isolates the divergence to the ARBITER (wave 07/08). Waveform-driven (not
theory) root cause of the reverted deadlock, peeled in layers as each fix landed:

  LAYER 1 (collision): the column FIRE (w_fire_out, pumice_cmd_arbiter.sv:247)
    gates on cmd_ready_i but NOT tCCD; tccd_ok_i is checked only at CLASSIFY and
    RELOADS ON FIRE, so a column is classified ~3 pipe-cycles before it fires and
    a 2nd same-bank column classifies against the stale (still-ok) tCCD -> both
    fire back-to-back -> DQ collision -> the write STRANDS (a later read sees
    UNINITIALIZED memory). The occupancy mask (w_col_inflight_bank) was hiding
    this by blocking the whole bank for the pipeline depth (-> the ~33% cap).

  FIX (landed, verified core_dfi past layers 1-2): FORWARD tCCD. Add t_ccd_i to
    the arbiter (wired from the scheduler); a column PICK (w_sel_*_col_f) reloads
    r_tccd_fwd = t_ccd_i-1; the column masks gate on w_tccd_fwd_ok (==0) INSTEAD
    of !w_col_inflight_bank. Columns now classify/fire exactly tCCD apart with
    the pipeline full; ACT/PRE to other banks fill the tCCD-off cycles. This
    removed the collision AND the hang (core_dfi ran to completion, 25s).

  LAYER 3 (remaining): with forward-tCCD, core_dfi now fails a DATA mismatch --
    a burst's beat 0 lands but beats 1-3 are 0 (the tail is lost), NOT a WAW/
    stale error. The column pacing is right; the burst's DATA drive is truncated.
    Next diagnosis: the serializer/CDC wrdata path under the new fire cadence
    (dfi_wr_serializer r_owed / wr_fire vs the burst length in the wrdata CDC).
    The 4-edit forward-tCCD change (port + counter + 2 masks + 1 wire) is the
    confirmed layer-1/2 fix; layer 3 is the last write-path FUB to scrub.

### FUB scrub layer 3+4 (2026-09-08): the COMPLETE arbiter fix -- core_dfi PASSES

The truncation (layer 3) was NOT the serializer/CDC. Root cause (t_ccd_i=1 in the
core test made the forward-tCCD a no-op there): with the occupancy mask gone,
NOTHING stopped the SAME entry being re-picked before its sch_valid self-clears
(1-cycle window) -> DOUBLE-COMMIT -> the cam drains the burst truncated. The
occupancy mask did THREE jobs: (1) per-bank tCCD pacing [forward-tCCD replaces],
(2) AP close serialization [r_ap_closing / *_guard already separate], and (3)
per-ENTRY double-issue prevention [the DEAD w_*_col_inflight_ent mask].

COMPLETE arbiter fix (both rd+wr masks): delete !w_col_inflight_bank, add
w_tccd_fwd_ok (forward-tCCD, reload on column pick) AND !w_*_col_inflight_ent
(the dead per-entry mask, now wired). Result: **core_dfi PASSES** (writes+reads
correct, no collision/hang/truncation), and 11/13 core tests pass (waw, b2b,
sched_order, fixed_open, close all green).

ONE remaining regression (layer 4): test_pumice_core_refresh_collide -- a read
returns ALL-ZERO within 64 cyc of a refresh. Passes on baseline. Cause: the
faster read issue puts MORE reads in-flight in the DFI (~50-cyc round trip) than
the refresh-drain waits for, so a read races the refresh PRE and lands on a
closed row. w_col_inflight_guard only tracks the 3-cycle PICK pipeline, not the
50-cycle DFI in-flight window. This is the READ path's wave-08 piece: the
refresh-drain must wait on the per-bank/global READ OUTSTANDING count (D), not
just the pick pipeline. (A write-only scoping -- reads on the old mask -- did NOT
cleanly isolate it; it hung, so the rd/wr coupling via the shared DQ/refresh
path is real. The full rd+wr fix is the right base; the refresh-drain wait is the
last change.)

NEXT: add read-outstanding tracking (wave 08) that the refresh-drain (refresh_ctrl
-> arbiter drain handshake) waits on before PRE-ing, then re-run refresh_collide +
refresh_credit + the full core suite, then board-validate write AND read BW.

### CORRECTION (2026-09-08, later): layer-4 theory DISPROVEN; occupancy mask is load-bearing for refresh

The "read races the refresh PRE / read-outstanding" theory above was WRONG.
Disproven by data, not argument: three separate arbiter changes -- (a) a
read-drain countdown gating the refresh PRE, (b) gating w_ref_safe on the LIVE
bank_row_active_i instead of the registered copy -- ALL left the failure at the
byte-identical sim timestamp (30690000). Inert changes = the REF timing does not
depend on any of them; my picture of the mechanism was wrong.

What it actually is (from the test's own GOLDEN readback, after neutralising the
heuristic zero-in-refresh checker so the sim ran to the data compare): a REAL
data corruption -- "refresh collided with 44/64 same-bank reads". The
CMD_HISTORY checker names it exactly: a REFab is granted while a bank ROW is
still OPEN (ACT with no intervening PRE). A plain OP_RD keeps the row open;
removing the occupancy mask (w_col_inflight_bank) let same-bank columns pipeline
tightly enough that the refresh REF lands on that open row and corrupts the
in-flight reads to it.

Decisive isolation: RESTORE only w_col_inflight_bank on both column masks (keep
forward-tCCD + per-entry guards) -> refresh_collide AND core_dfi both PASS. So
the occupancy mask's per-bank column serialisation is LOAD-BEARING for refresh
sequencing, not merely a throughput throttle.

And the throughput consequence: with the occupancy mask retained, forward-tCCD
and the per-entry guards are strictly MORE-restrictive AND-terms that the mask
already dominates -- they add no same-bank throughput (verified: HEAD passes
core_dfi on its own; the added terms only narrow the pick). The wave-07 win
(delete the mask for tCCD-rate same-bank streaming) is therefore BLOCKED on
making the refresh path robust to pipelined same-bank columns -- the refresh
must quiesce/precharge a bank whose column stream is still in flight before it
REFs. Until that exists, the mask stays and HEAD is the correct baseline:
cross-bank columns (the dominant bandwidth driver) still pipeline freely; only
same-bank back-to-back is throttled.

STATE AT HEAD (verified 2026-09-08): full core suite 12/13. The one failure,
test_pumice_core_perf_paging_sched_cross, is PRE-EXISTING at HEAD (static_close x
order_in_order measures 37.8%, below the 45% floor) and unrelated to any of this.
All exploratory arbiter/scheduler edits were reverted to HEAD; kept from this
scrub: the wr_data_cam WAVE10 regression test and this write-up.

SEPARATE latent finding worth a ticket: pumice_cmd_history_checker.sv samples on
cmd_valid_i with NO cmd_ready gate (no ready port at all), so during DFI
back-pressure it records commands the arbiter only PRESENTED, not ones the DFI
accepted -- its row-open model can diverge from the real command stream. Not the
cause of the corruption above (the golden compare is independent), but it makes
the checker unreliable under back-pressure and should gate on valid && ready.

NEXT (for the throughput push, when resumed): make the refresh drain robust to a
live same-bank column stream so w_col_inflight_bank can be dropped -- that is the
real wave-07/08 work, and it is a refresh-sequencing change, NOT a read-path one.

### CORRECTION 2 (2026-09-08): refresh_collide is NOT a refresh bug -- it is a same-bank in-flight-column data hazard

Pursuing the "refresh-sequencing fix" turned up conclusive data that the failure
is mis-named. With the occupancy mask removed, refresh_collide fails, but:

  * CMD_HISTORY (u_cmd_history, instantiated with .cmd_valid_i(cmd_valid_o &&
    cmd_ready_i) -- i.e. correctly READY-GATED, it audits the accepted DRAM-bound
    stream) reports ZERO REFab-while-row-open violations (106 REF debug prints,
    0 $fatal). Sequencing is LEGAL. The test's own assertion text ("see
    CMD_HISTORY assertions for the REFab-while-row-open violation") is the
    author's HYPOTHESIS, not what fires -- the golden DATA compare is what fails.
    (page_policy=1/CLOSE means every access is ACT+RDA, so no REF ever meets an
    open row; the refresh angle is a red herring for this failure.)

  * Spacing-independent: t_ccd_i = 1, 2 and 4 (clean rebuilds) ALL fail at the
    byte-identical sim time (30690000). So it is NOT a DQ / column-spacing
    collision -- forward-tCCD (a global, pick-timed tCCD gate) does not change
    it. (The core test's t_ccd_i=1 is separately unphysical for BL8 and should be
    a realistic 2-4; the board regmap default is 4. But that is not the cause.)

  * ONLY w_col_inflight_bank (the per-bank "a column to this bank is already in
    the pick pipeline" block) prevents it. Restoring just that mask -> pass.

Conclusion: the hazard is TWO same-bank column accesses in flight at once
corrupting through shared per-bank state (open-row / auto-precharge bookkeeping
in bank_timer, or the wr_data_cam/rd_cmd_cam same-bank path), NOT refresh and
NOT the DQ bus. The occupancy mask serialises same-bank accesses and hides it.

Therefore the wave-07 win (drop the mask for tCCD-rate same-bank streaming) is
blocked on a per-bank same-bank-pipelining interlock -- allow same-bank columns
to pipeline on open-page HITS while serialising the ACT+auto-precharge sequence
-- NOT on any refresh-path change. This supersedes the "refresh-sequencing fix"
framing. NEXT: localise the shared per-bank state that two in-flight same-bank
CLOSE-policy accesses corrupt (bank_timer row/ap bookkeeping is the prime
suspect), reproduce it in a bank_timer/arbiter FUB test at realistic t_ccd, fix
the interlock, THEN drop w_col_inflight_bank and re-run the full core suite +
board-validate (with refresh on -- HEAD refresh is already correct).

### ROOT CAUSE FOUND (2026-09-08): DFI WR command has no write-data backpressure

Instrumented the mask-removed CLOSE-policy failure end to end. Boundary counts
are ALL 64 (nothing is dropped at any handshake): CAM fills(wd_last)=64,
CAM commit_done=64, serializer wr_fires=64, serializer burst_lasts=64, DFI
WR=64. The serializer drives all 64 bursts with CORRECT non-zero data
(zero_bursts=0, data_or = k<<16|0xab3 per burst k). Yet 32 (odd) writes land as
ZERO at the PHY. The smoking gun: SER_DBG STARVE_CYC=463 -- the serializer is
"owed a drive but wd_valid=0" for 463 cycles, i.e. it drives LATE, past the
fixed write latency the PHY samples at, so the PHY captures zero for the
misaligned bursts.

Mechanism: the DFI CDC (pumice_dfi_cdc) crosses the COMMAND stream and the WRITE
DATA on TWO SEPARATE async FIFOs. On dfi_clk the serializer drains 1 DFI word/
cycle -- FASTER than the CAM fills the wd FIFO on the slower ctl/aclk -- so if a
WR command is issued before its whole burst is staged, the serializer runs dry
mid-burst and drives late. pumice_dfi_cmd_path gates READ issue on rd_op_ready_i
(the aligner has a slot) but has NO symmetric gate for WRITES -- it issues WR
commands blind to write-data readiness. The occupancy mask (w_col_inflight_bank)
was incidentally throttling the commit cadence enough to keep the wd FIFO ahead;
removing it lets the command outrun its data. CLOSE-policy-only because OPEN
streams same-row writes back-to-back keeping the wd FIFO full, whereas CLOSE's
ACT+auto-precharge cadence lets the command path get ahead. Spacing-independent
(t_ccd 1/2/4 identical) and NOT refresh (CMD_HISTORY, ready-gated, 0 violations;
it also does not even check tCCD). This is a REAL board bug, not a model artifact.

FIX (in progress): add a symmetric write-data backpressure. A "write burst
staged" token (pushed in the CDC on each wd_last entering the wd FIFO, crossed to
dfi_clk via a token FIFO like the init/level ones) gates the cmd_path WR issue:
w_gate &&= (!w_is_wr || wr_burst_ready_i); pop one token per WR fire. The WR
command then never precedes its fully-staged burst, the serializer never starves,
and the fixed-WL contract holds -- so w_col_inflight_bank can finally be dropped.

### CORRECTION 3 (2026-09-08): DFI write-backpressure fixed starvation but NOT the corruption

Implemented the write-data backpressure (a "write burst staged" token FIFO in
pumice_dfi_cdc gating pumice_dfi_cmd_path's WR issue, symmetric to the read
rd_op_ready_i). It WORKS at what it targets: STARVE_CYC 463 -> 0 (the serializer
no longer drives dry), and it passes with the occupancy mask still present (full
compile, refresh_collide 22s, no regression). It is a genuine latent bug -- the
write path lacked the read path's backpressure -- worth revisiting.

But it does NOT fix the mask-removed corruption: golden bad = 44/64 (WORSE than
the 32/64 without it), with STARVE=0. So starvation was real but not the cause.
And the fire spacing is already correct: pumice_dfi_cmd_path paces column FIRES
by COL_BURST_CYC = BL_WORDS (r_col_pace), so bursts are >= BL_WORDS apart and the
serializer's owed count stays 1 -- no contiguous-drive misalignment. Yet with
data staged, fires paced, owed=1, and each burst driven at its own t_phy_wrlat,
32-44 same-bank CLOSE-policy writes still land as ZERO at the PHY.

So the remaining cause is NOT: refresh (CMD_HISTORY clean), command drop (all 64
WR issue), serializer content (drives all 64 correct, zero_bursts=0), serializer
starvation (fixed, =0), DQ/tCCD spacing (t_ccd 1/2/4 identical; COL_BURST_CYC ok),
or fill-vs-commit (CAM sch_valid already requires r_fdone). It is CLOSE-policy-
specific (OPEN passes mask-removed) and only w_col_inflight_bank prevents it.
Prime remaining suspects: (a) write ADDRESS/column mis-computed for a pipelined
same-bank second access (data written to the wrong column -> read of the right
column returns zero), or (b) the CLOSE auto-precharge state (r_ap_closing / the
ACT-WRA-autoPRE sequence) corrupting when a second same-bank access enters the
pipeline before the first's precharge resolves. NEXT DIAGNOSTIC: log the actual
DFI WR command {bank,row,col} vs the AXI write address for the bad (odd) writes
-- if the column differs, it is (a); capture at the DFISlavePHY write handler.

All RTL reverted to HEAD (the DFI backpressure adds a CDC token FIFO on the
board-critical path for no benefit while the mask stays, and made mask-removed
WORSE). HEAD remains the correct baseline; refresh works on it. The DFI
backpressure patch is preserved in the session scratchpad if revisited.

### CORRECTION 4 (2026-09-08): write side proven fully correct; residual is DFI WL alignment

Logged every DFI WR command's {bank,row,col} at the arbiter for the mask-removed
CLOSE run: all 64 are correct -- bank 3, one row, columns 0,8,16,...,504, all
OP_WRA, 64 distinct. Combined with the earlier proofs (serializer drives all 64
bursts with correct data, zero_bursts=0; 64 WR commands at the PHY; 64 CAM
commits/fills), the ENTIRE write side is provably correct: address, data,
command, and count all right. The corruption is therefore purely a DFI
command<->wrdata WRITE-LATENCY alignment (or DFISlavePHY capture) effect: correct
data is presented but the PHY writes zero for ~half the same-bank CLOSE-policy
bursts when the occupancy mask is gone. Source-level fixes (write backpressure,
fire pacing) did not resolve it. NEXT (decisive, not yet done): capture a VCD of
one corrupted write and inspect dfi_wrdata / dfi_wrdata_en phase vs the DFI WR
command at the DFISlavePHY -- a protocol-level look, the one diagnostic still
outstanding. Until then w_col_inflight_bank stays and HEAD is the correct
baseline (12/13, refresh working).

### VCD DIVE (2026-09-08): corruption is DFI read-DATA-RETURN alignment, not the write path

Instrumented the DFISlavePHY write commit (DFI_WR_TRACE) and read serve, plus the
arbiter WR/RD command addresses, for the mask-removed CLOSE run. Findings, in
order, each proven:

  * WRITE side is fully CORRECT. Arbiter WR commands: bank 3, one row, cols
    0,8,16,...,504, all OP_WRA. DFISlavePHY commits: every write's real data
    lands at its byte address (0x56000=AB0, 0x56040=1AB0, ...), committed exactly
    ONCE, no clobber. (Each DFI cycle carries 2 device words: phase0 = real data,
    phase1 = zero -- that interleave is the normal layout; k=0 reads phase0 and
    passes.)
  * READ COMMANDS are fully CORRECT. Arbiter RD commands: bank 3, cols
    0,8,16,...,504, all OP_RDA -- IDENTICAL columns to the writes. So the read
    addresses/decode are right; the data is in memory at those addresses.
  * Yet the golden AXI read for every ODD k returns ALL-ZERO (not the interleave)
    while EVEN k is correct. Command right + data-in-memory right + read all-zero
    => the loss is in the DFI read-DATA-RETURN path (pumice_dfi_rd_aligner /
    pumice_rd_cmd_cam), NOT the write path and NOT addressing.

This is the READ ANALOG of the write-serializer starvation found earlier: the
DFISlavePHY drives rddata at command_cycle + read_latency; the rd_aligner
captures at t_rddata_en_i -- a fixed-latency contract. When same-bank reads
pipeline (mask removed), that capture misaligns for alternate reads and their
data is lost -> all-zero. So BOTH DFI data paths (wr serializer, rd aligner) have
the same class of fixed-latency-vs-pipelined-cadence hazard, and w_col_inflight_bank
(the occupancy mask) is the blunt throttle that keeps both aligned.

CONCLUSION: removing the mask for same-bank throughput (wave-07) requires
DFI-layer data-alignment hardening on BOTH paths -- the write-burst-staged
backpressure prototype (this turn) for writes, and an equivalent read-return
alignment/backpressure for reads -- not a single localized fix. This is a real
DFI-layer project, distinct from refresh (which is correct) and the arbiter.
HEAD stays the correct baseline (12/13, refresh + reads/writes all correct with
the mask in place). NEXT: design the read-return alignment (rd_aligner capture
gated to the actual return, mirroring the write token), validate both paths on
the FUB tests, then drop w_col_inflight_bank and re-run core + board.

### CORRECTION 5 (2026-09-08, session restart): the "DFI read-return alignment" residual is the arbiter's auto-precharge stale-image hazard -- proven with the model's own command trace

The VCD-dive conclusion above was an inference ("commands correct + data in
memory + reads zero => return path"). "Commands correct" only meant the ADDRESSES
were right. The DFISlavePHY has a direct detector for the real hazard that was
never consulted: `DFI_CMD_TRACE=1` logs every decoded command with the bank's
open row at decode time, and prints `open_row=closed` when a column command hits
a bank with no open row. On such a read the model serves `.row or 0` -> ROW 0,
which was never written -> ALL-ZERO. `no_act_before_rd` is a SOFT violation and
the core test demotes everything to soft, so it only ever logged a warning.

Run A (HEAD, `!w_col_inflight_bank` deleted from both column masks, the dead
per-entry `w_*_col_inflight_ent` masks wired in), refresh_collide, CLOSE policy:

    @30566ns RD  bank=3 addr=0x400 open_row=0x5      <- k=0, its own ACT
    @30582ns RD  bank=3 addr=0x408 open_row=closed   <- k=1: NO ACT, bank closed by k=0's RDA
    @30598ns RD  bank=3 addr=0x410 open_row=closed
    @30614ns RD  bank=3 addr=0x418 open_row=closed

The previous "byte-identical failure timestamp 30690000" is 30690 ns -- the
golden compare firing right after these. Mechanism: k=0 is RDA (A10 set); the
model (correctly, and the real device effectively) closes the bank; the arbiter
classified k=1..3 as row HITS against the REGISTERED row image (still "open",
`r_ap_closing` only engages at FIRE, ~3 pipeline cycles after k=0's classify),
so they issue as columns to a closed bank with no re-ACT. The occupancy mask
was the only thing covering that pre-fire window -- exactly what its own comment
says ("Covers RDA1's ~3 pipeline cycles ... gated by f_ap(b)"), except the code
applied it UNCONDITIONALLY, which is the same-bank throughput cap.

Raw mask removal alone (no per-entry mask) fails earlier and differently: the
FIRST write fires three times (`WR addr=0x400 open_row=0x5`, then twice more
`open_row=closed` 4 and 8 cycles later) -- the per-entry re-pick double-issue --
and every odd write times out waiting for B. So "odd writes / odd reads are
zero" was the per-entry double-issue and the AP stale-image hazard, seen from
two different fix states. Nothing in the DFI layer is implicated.

FIX (run B, both column masks): keep the occupancy mask ONLY when the bank's
column would auto-precharge, and wire the per-entry mask:

    rd_col_m[e] = ... && !(f_ap(rb) && w_col_inflight_bank[rb]) && !r_ap_closing[rb] && !w_rd_col_inflight_ent[e] ...
    wr_col_m[e] = ... && !(f_ap(wb) && w_col_inflight_bank[wb]) && !r_ap_closing[wb] && !w_wr_col_inflight_ent[e] ...

Under CLOSE this is bit-identical to HEAD (the AP sequence ACT->xDA->PRE cannot
pipeline same-bank columns anyway); under OPEN same-bank columns stream.
Verified (clean builds, DFI_CMD_TRACE on):
  * refresh_collide (CLOSE): PASS, 64 reads, 75 REFs, 0 columns to a closed bank, 148 ACTs on bank 3.
  * core_dfi (OPEN, the run that deadlocked with the earlier f_ap-only attempt): PASS.
  * test_pumice_arbiter_issue_rate: 200 fires / 200 cycles = 1.000 (HEAD ~0.5).
  * cmd_arbiter FUB: PASS.
  * top suite (make clean-all && make run-all-full-parallel): 114 passed, 1 failed = the pre-existing perf_paging_sched_cross (static_close x in_order 37.8%, byte-identical to HEAD, PUMICE-021).
Open design point: `f_ap(b)` is evaluated at classify time but the emitted op's
AP bit is decided at the output stage; with the adaptive page-policy modes
(`ap_close_i[b]` changing mid-pipeline) there is a <=3-cycle window where a
column classified with f_ap=0 can follow an in-flight column that outputs as
xDA. Carrying the AP decision with the pick (decide at classify, emit what was
decided) closes it; not needed for static OPEN/CLOSE.

Forward-tCCD (layer 1) is NOT part of this fix: the core tests run t_ccd_i=1 and
the board's BL4 @ DFI_RATE=2 makes one column per aclk the legal rate, so the
DFI cmd_path's exact COL_BURST_CYC pacing is the real DQ-occupancy guard.

### BOARD FINDING (2026-09-08): the tCCD CSR is never programmed -- default 4 aclk = 8 CK

`pumice_csr.rdl` TIMINGS_RRD_FAW_WTR_CCD.tCCD resets to 4 (aclk cycles). No
host path writes that register (only TIMINGS_RFC_REFI and PHY_TIMING are
programmed), so every board measurement to date ran with a GLOBAL (all banks,
both directions) column-to-column gate of 4 aclk = 8 DRAM CK, against a JEDEC
DDR2 tCCD of 2 CK = 1 aclk. `global_timers` reloads one shared counter on every
column FIRE and the arbiter checks the flopped `tccd_ok_i` at CLASSIFY (3
pipeline stages earlier), so the gate is porous for the pipeline depth then
closed for ~4+3 cycles: bursts of 3-4 columns then an ~8-9 cycle bubble. That is
the ILA cadence measured above (1054x gap-1 / 259x gap-9, 33% duty), on a
bank-ROTATING workload the same-bank mask does not touch. The sim never sees
this because the core tests poke t_ccd_i=1 directly. Zero-RTL experiment:
program tCCD=1 (or 0, letting COL_BURST_CYC pace) and re-measure.

### LiteDRAM cross-check (2026-09-08): no DFI data-path alignment hardening is needed

Checked against the reference that reaches ~85% on this board
(`litedram/core/multiplexer.py`, `phy/s7ddrphy.py`, `modules.py`):
  * `MT47H64M16` declares `tCCD=(2 CK)`; `ck_to_cycles` at 1:2 gives ONE
    controller cycle. `tXXDController(tCCD)` is the only column gate
    (`cas_allowed`); columns issue every cycle.
  * The multiplexer drives `phase.rddata_en` / `wrdata_en` from `is_read` /
    `is_write` of the chosen command ON THE SAME PHASE as the CAS. There is no
    per-read tracking and no alignment logic in the controller.
  * The PHY returns `rddata_valid` as `rddata_en` delayed by a fixed
    `read_latency = cl_sys_latency + 6`; the data path is a pure fixed-latency
    pipeline that tolerates any command cadence.
`pumice_dfi_rd_aligner`'s rddata_en shift-register delay line and per-read
capture counter are the same construct, and `pumice_dfi_wr_serializer` drives
at a fixed t_phy_wrlat. Both were already verified cadence-agnostic by their
FUB tests. The "alignment issue" in the log above was the arbiter's closed-bank
column (CORRECTION 5), never the DFI layer. The dfi_layer block is CLOSED as
not needed; the wave-01/02/10 cadences are what the layer already does.

### TIMING AUDIT (2026-09-08): the board runs every JEDEC timing at the RDL reset

`pumice_top.sv:224-234` wires the timers straight from `hwif_out.TIMINGS_*`;
`pumice_device.py` wrote only PHY_TIMING / DFI_PHASE / MRx / ADDR_MAP / PAGE_* /
SCHED_TUNING / REFRESH_TUNING / tREFI. The sim pokes its own set. In MC cycles
(75 MHz, 2 CK per cycle, MT47H64M16HR ns values as in RDS-DV jedec/ddr2-*.csv):

    param   RDL reset  sim poke  JEDEC@75MHz  LiteDRAM@75MHz   note
    tRCD       15         3          2             2            reset = 200 ns vs 15 ns
    tRP        15         3          2             2
    tRAS       40         4          4             (unenforced)
    tRC        60         6          5             (unenforced)
    tWR        15         3          2             2
    tRTP        4         2          1             (unenforced)  2 CK min
    tRRD        6         2          1             (unenforced)  2 CK min
    tFAW       35         6          4             (unenforced)
    tRFC       16         8         10            11
    tREFI    1950      1024        585           586            reset = 26 us vs 7.8 us
    tCCD        4         1          1             1            reset = 8 CK vs 2 CK
    tWTR        4         2          3 (cmd->cmd)  4
    tRTW        6         2          3 (cmd->cmd)  (RTW FSM)

Consequences on the board: every page miss paid ~200 ns of tRCD and ~200 ns of
tRP (the "OPEN policy 8.8x" win was mostly this); the porous global tCCD=4 gate
produced the ILA 3-columns-then-9-idle cadence (33% write duty); and refresh ran
3.3x slower than JEDEC. Host fix (the host commit that follows): `ddr2_timings_mc_cycles()` +
`Pumice.set_jedec_timings()` in pumice_device.py, applied by every
`pumice_char.ControllerConfig` (default ON, `TEST_JEDEC_TIMINGS=0` for an A/B,
`PUMICE_MC_CLK_HZ` selects the clock -- 100 MHz default is never-fewer-cycles
safe on the 75 MHz board). tWTR/tRTW are command-to-command distances (what the
RTL's global counters measure), derived as WL+BL/2+tWTR and CL+BL/2+2-WL.

### READ RETURN RING (2026-09-08): in-flight reads decoupled from the scheduling CAM

Board read bandwidth was a Little's-law bound, not an issue-rate problem: a
read held its `pumice_rd_cmd_cam` entry from AR to R-drain, so 8 entries over a
~27-cycle DRAM round trip cap at 8 x 8 B / 27 = ~180 MB/s -- the measured
179.9. (The ILA's "reads starved at issue, r_outstanding mean 0.37" was a window
where the single-outstanding read generator had nothing to offer; see below.)

Split (Sean's direction: "free the CAM entry if the response can be assigned
when the data returns"):
  * `pumice_rd_cmd_cam` = scheduling window only. Entry lives insert -> ISSUE,
    carries a TICKET. Issue frees it and forwards the ticket.
  * `pumice_rd_return_ring` (new fub) = the reads in flight. AR-order ring,
    ticket = slot; issue-order FIFO maps each returning DFI burst to its slot;
    per-slot ready bit; head drains in AR order when complete; frees on the last
    drained beat. FSM-free (two pointers + ready bits + one FIFO + one BRAM), no
    age matrix. A fetch pointer runs ahead of the head through the 2-deep BRAM
    skid so one-beat slots (the board) stream at a beat per cycle.
  * `RD_RET_DEPTH` (32) is a new top parameter; the DFI aligner tracking and the
    return CDC FIFO scale with it (RD_RET_DEPTH x BURST_WORDS), because
    dfi_rddata_valid has no backpressure -- caught by the aligner's own sizing
    assertion on the first run (return FIFO still 32 words, 11 reads x 4 words
    in flight at the TB's 2.5x DFI clock).
  Spec: `waves/12_rd_return_ring.json`.

Verified: ring FUB test (reorder, AR-order hold, partial head, full/free, 3x
wrap under drain backpressure; DEPTH 8/32, 1 and 4 beats); rd_cmd_cam FUB test
(ticket forward, free-at-issue, slot reuse, window full, iss backpressure,
head_rel); axi4_ifc macro; new core test `perf_read_inflight` (strict DFI read
latency 200 = 80 aclk, page-hit stream): RD_RET_DEPTH=32 -> 0.91 beats/cycle,
RD_RET_DEPTH=8 (the old bound, mutation) -> 0.31 RED.

**CORRECTION (2026-09-09).** The "one outstanding AR" caveat first written
here came from the read generator's STALE header comment. Its AR path is
decoupled from R (`fub_arvalid` does not wait for rlast) and issues as long as
the slave accepts, so the board's 180 MB/s really was the controller's 8-entry
Little's-law bound, which the ring lifts. Both generators now carry a
`MAX_OUTSTANDING` parameter (default 8; `GEN_MAX_OUTSTANDING` on
ddr2_char_macro) so the in-flight window a DUT sees is explicit and bounded.
Reads still assume R bursts arrive in AR order (same-id, or a controller that
returns in AR order, which pumice does).

### WRITE-BURST-STAGED GATE (2026-09-08): the char sim caught what the pumice suites did not

The arbiter fix (a68856cb6) passed every pumice fub/macro/top suite and then
FAILED 7 tests of the ddr2_char_framework sim -- all x16 (the BOARD device
config: DRAM_DEVICE_WIDTH=16, strict write timing, t_phy_wrlat=0) plus
`concurrent`. Bisected in a detached worktree: pre-session 4 pre-existing
failures (faithful / rdphase1 / strict / x16_free_earlyen); the arbiter commit
adds 7; the ring commit adds none; JEDEC timings add `char_families_x16`.
Symptom: `engine did not finish: wr True, rd False, mism 12..25` -- reads hang.

Isolation by experiment (one mask at a time restored to unconditional):
    read mask restored only   -> still FAILS
    write mask restored only  -> PASSES
So it is the WRITE side: under OPEN policy same-bank WR columns now issue every
cycle, the WR command crosses the cmd CDC FIFO and reaches pumice_dfi_cmd_path
before its data has crossed the (separate) wrdata CDC FIFO, and the serializer
drives late. At t_phy_wrlat=0 the strict PHY captures whatever is on the bus.
The occupancy mask had been hiding this by spacing same-bank writes ~3 cycles
apart. pumice_dfi_cmd_path gated READs on the aligner's rd_op_ready_i and had
NO write equivalent -- the "genuine latent bug" the log above found and set
aside as not-this-failure.

First fix tried: a DFI-side gate -- pumice_dfi_cdc pushes a "burst staged"
token on the ctl edge that accepts a burst's LAST wrdata word (data and token
FIFOs accept atomically, same N_FLOP_CROSS synchronizer so the token is never
visible before the data); pumice_dfi_cmd_path holds a WR until a token is
present and pops it on accept. It fixed the x16 smoke (PASS; fails without) and
the dfi FUB/macro tests -- and then the top suite failed refresh_credit and
perf_refresh_bubbles with the TB command-history checker fatal ("ACT only 1
cyc after REFab", "ACT 3 cyc after PRE"), READY-gated (the checker is now bound
to the accepted stream; its valid-only binding was the latent fault the log
above flagged). Not an artifact: the scheduler's cmd FIFO (8) + the cmd CDC
(8) sit between the timing-enforcing arbiter and the DFI. A stalled WR at the
DFI head lets up to 16 commands queue with their arbiter spacing intact, and
when the stall clears they drain back-to-back -- tRFC/tRP compressed at the
DRAM. ANY stall the arbiter's timers do not see does this; the write gate just
made stalls frequent (rd_op_ready and COL_BURST_CYC pacing are the other two
sources and are config-avoidable).

Measured why the gate stalls so much (probe in pumice_core, perf_write_ceiling,
BL8): the burst's last data word lands in the wrdata CDC **20 aclk after** its
WR command entered the cmd CDC, in steady state (241/256; 5 cycles for the
first few before the queue builds). The arbiter runs the command stream up to
the FIFO capacity ahead of the data, which drains at the DFI's own rate.

STOPGAP (this commit): BOTH column masks return to unconditional (the AP
carry and the per-entry double-issue guards stay). Gating only the read side
let a read front-run a masked same-bank write inside the write-batching drain
(cmd_arbiter FUB "wm 3/1 fire order"), so the two lift together. The DFI gate
is NOT merged. The issue-rate FUB floor is parked at 0.5 (measured 1.000 with
the AP-gated masks; restore the 0.95 floor with the next block). HEAD is green
on the pumice suites AND the char sim.

NEXT BLOCK -- "WRITE DATA MUST LEAD" (design, for Sean's review):
  1. Rate-match the WR commit to the drain: wr_commit_ready = drain queue has
     at most ONE burst queued (today: 8). The data path then never trails by a
     queue, only by its fixed pipeline latency L_d (~5 aclk at BL8, ~2 at BL4
     x16). No bandwidth cost: one WR per BL_WORDS cycles is the DQ rate.
  2. A fixed D-stage delay on the WHOLE command stream (scheduler -> cmd CDC),
     D >= L_d - L_cmd, so every WR reaches the DFI no earlier than its data.
     Spacing is preserved exactly (every command delayed alike); latency +D.
  3. Keep the staged-token gate as a CHECKED invariant (never expected to
     stall; count engagements, assert zero in the ceiling tests).
  4. Keep t_ccd >= BURST_WORDS so COL_BURST_CYC pacing never stalls either
     (the core sim's t_ccd=1 at BL8 is the unphysical case).
  Timing note: `make synth` ends by printing `make timing`, which shows the
  LATEST POST-ROUTE report (fpga/reports/timing_summary.txt) -- this morning's
  bitstream, not the synthesis just run. The fresh post-synth numbers are in
  fpga/reports/timing_summary_synth.txt: 32c3a9cdc = WNS +0.885 ns at 75 MHz,
  0 failing endpoints of 86376, LUT 45.5%, FF 20.7%.

  This is what LiteDRAM does structurally: the multiplexer drives the DFI
  directly and a write command is only chosen once its data is at the head of
  the write FIFO -- no command queue downstream of the timing decision.

LESSON (for the regressions rule): the pumice component suites do NOT run the
board's x16 / strict-timing configuration. `ddr2_char_framework/dv/tests`
(test_ddr2_char_uart + test_ddr2_char_char) is the board gate and must run
before any pumice RTL commit; its Makefile's run-all target points at a test
name that no longer exists (`test_ddr2_char_macro[all-full-parallel]`), so it
had silently stopped being a gate.

### WRITE DATA MUST LEAD -- implemented (2026-09-09)

Sean: "Rate match the write." Three pieces, each a few lines:

  1. `pumice_wr_data_cam`: `commit_ready` = drain-queue occupancy <
     `WR_DRAIN_AHEAD` (2): a WR commits only while at most one burst waits
     behind the one being fetched, so its data trails the command by a fixed
     pipeline latency, never by a queue. Occupancy is a registered counter
     (the FIFO's combinational `count` made a Verilator UNOPTFLAT loop).
  2. `pumice_mem_cmd_scheduler`: every command leaves the cmd FIFO exactly
     `CMD_DELAY` (6) cycles after it entered -- a token shift register + a
     matured-token counter gate the FIFO head. Spacing preserved exactly, and
     a WR's data reaches the DFI before the command does. CMD_FIFO_DEPTH 16.
  3. `pumice_dfi_cdc` / `pumice_dfi_cmd_path`: the write-burst-staged token
     gate, now an INVARIANT: `r_wr_held_cnt` / `r_wr_held_max` count the
     cycles a WR ever waits at the DFI head; the write-ceiling core test
     asserts zero and every sim prints them at `final`.

One more arbiter fix fell out: the CAM's `commit_ready` / the ring's
`issue_ready` were checked at CLASSIFY only. With a rate-matched commit they
drop often, so a write could FIRE into the cmd FIFO while the CAM refused the
commit -- a DRAM WR whose data never drains, and the staged gate then holds
forever (AW/W/AR timeouts in four core tests). Both readies are re-checked
LIVE at the output stage (a bubble, re-picked next round).

Four more things the core suite then forced, each found from a measurement:

  4. `CMD_DELAY` scales with the burst: at BL8 (4 DFI words) the token needs
     the LAST word, so the lag is ~5 + 2 x BURST_WORDS (13; the board's BL4
     x16 needs 7). Default 0 = auto in pumice_core. And the wrdata CDC must
     hold the bursts staged during that delay: WD_FIFO_DEPTH 16 -> 32, else
     it fills, the drain stalls and the lag is back (held 6 at D=13).
  5. The commit predicate is DECISION-time: the arbiter decides a write one
     cycle before it fires, so `commit_ready` reports the occupancy after
     this cycle's own accept and pop. Without it two back-to-back writes let
     the second fire into the cmd FIFO while the CAM refused it -- a DRAM WR
     with no data behind it, and the staged gate held for 29373 cycles.
     The arbiter also re-checks `wr_commit_ready_i` / `rd_issue_ready_i`
     LIVE at its output stage, and (same class, found by probe) the ACT
     gate `w_act_gate_live`: an ACT selected in the one cycle between a
     refresh's tRFC expiring and the next pulled-in REF firing reached the
     output with rfc_busy set -- "ACT only 2 cyc after REFab".
  6. The write CAM frees its entry at FETCH-last, not consume-last (the
     prior session's Fix B, then a null result; now load-bearing): with the
     command delayed, consume-last held each entry ~30 cycles and 8 entries
     could not cover a burst every 4 -- W back-pressure 222 cycles in the
     write ceiling. The B strobe rides the skid tag, so nothing needs the
     entry after fetch.
  7. Forward tCCD (the prior session's layer-1 fix) REPLACES the flopped
     global `tccd_ok_i` on the column masks: reload on column SELECTION,
     `<= 1` so the period is exactly tCCD, plus a same-cycle-selection term
     for tCCD > 1. Stacked with the fire-reloaded gate the period was tCCD+4
     (read throughput halved at tCCD=4). pumice_core clamps t_ccd to
     >= BURST_WORDS and the core tests now poke the physical 4 for BL8 (the
     old 1 bunched columns into COL_BURST_CYC stalls -- a compression source).

  8. Refresh-pending column block. With the AP-gated masks and tCCD=1 the
     x16 `reorder` scenario LIVELOCKED: refresh pending, bank 0 open, eight
     row-hit entries. The refresh branch has absolute priority and waits for
     a PRE of bank 0, but the pick pipeline re-selects a bank-0 column every
     cycle and that selection's in-flight guard blocks that PRE. The old
     unconditional mask broke the loop by accident (a re-selected same-bank
     column masked itself the next cycle). Now columns to the banks a pending
     refresh will close are not selectable (all banks for REFab, the rotor
     bank for REFpb). Found from the final-state probe: refresh_req=1,
     row_active=00000001, wr/rd_sch_valid=11111111, pick_valid=0.

With that, BOTH column masks are AP-gated again (columns at tCCD on OPEN rows,
issue-rate FUB floor back to 0.95), and:
  * x16 char smoke / concurrent / sweep_x16 / pagehit_x16 (strict write,
    t_phy_wrlat=0): PASS, gate held 0 cycles in every one.
  * core: write ceiling (held 0 asserted), read in-flight, refresh_credit,
    refresh_bubbles, core_dfi, refresh_collide, waw, b2b: pass.
  * dfi cmd_path/cdc FUB, wr_data_cam FUB (WAVE10 re-scoped to the rate-
    matched contract), arbiter FUBs (issue rate 1.000), macros: pass.
  Full suite + char A/B + synth results: see the commit.

Test-side notes: `_bring_up` settles 40 cycles after init_done (the init's two
REFs now reach the DFI through the delay AFTER init_done -- they were counted
"inside a parked window"); the write-stream TB-starvation metric is AW-aware
(W offering nothing while the DUT holds AW is the DUT's back-pressure) with an
8% budget for the engine's per-burst refill gap under a physical tCCD.

### PAGING MODES RESTORED (2026-09-09): adapt_access / rbl_static / rbl_dyn back in the base build

User ask: "add more paging and scheduling options from the ones removed if
timing passes now". Three tiers, each gated on the 75 MHz post-route build:

  B. PAGE_POLICY_CFG.policy_mode 5/6/7 (pumice_row_pred_table, pumice_rbl_table,
     the PAGE_RBL_CFG register and the ctr_width/ctr_open_max/ctr_init fields)
     -- reverted ae8678975 + 1151b1c57 back in. DONE, see below.
  A. The ORDER_MODE overlays (in_order / age_threshold, +define+PUMICE_ENHANCED)
     in the board bitstream -- env PUMICE_ENHANCED=1 on create_project.tcl.
  C. The two-stage bank scheduler (rtl/OLD/pumice_bank_cmd_picker +
     pumice_bank_sched_core) as +define+PUMICE_BANK_SCHED. NOT restored: every
     hazard fix of the last two sessions (AP-gated occupancy mask, forward
     tCCD, live output re-checks, refresh column block, per-entry double-issue
     guard, ring issue notify, decision-time commit ready) lives in the flat
     arbiter's pick pipeline and would have to be re-derived inside the two-
     stage picker. That is a port, not a revert; held for a go/no-go.

TIMING CORRECTION FIRST. Every synth/route number quoted above this section
("+1.117 ns at 75 MHz", "+0.885 ns at 75 MHz", this morning's post-route
+0.083 ns) was measured on the DEFAULT profile: the clock table in those
reports shows w_sys_i at 15.000 ns = 66.67 MHz. The 75 MHz / DDR2-300 profile
is +define+PUMICE_SYS_75, selected by env PUMICE_SYS_75=1 on `make bitstream`
(create_project.tcl prints `verilog_define: PUMICE_SYS_75` when it is on --
grep the build log for that line before believing a number). Only the
numbers in this section are 75 MHz numbers.

One more build-hygiene note: a build in a detached worktree still reads the
pumice sources from the MAIN tree unless REPO_ROOT is overridden (env_python
exports REPO_ROOT and the sub-filelists resolve through it), and the
fpga_flow lock refuses to start while ANY vivado is running, so A/B builds are
serial.

Restoration findings:
  1. The predictors learned nothing (adapt_access: 12 PREs vs baseline 11).
     page_policy's command taps were fed from the scheduler's FIFO OUTPUT
     (`cmd_valid_o && cmd_ready_i`), which now releases CMD_DELAY cycles after
     the arbiter's decision (13 in the BL8 sim), while the bank image the
     predictors correlate against (`bank_row_active_i`/`bank_open_row_i`) is
     live. Moved the taps to the arbiter's accept (`a_cmd_valid && a_cmd_ready`
     + a_cmd_op/bank/row) -- the same stream the scheduler's own ready-gated
     history checker watches. rbl / acc / fixed_open pass.
  2. paging_sched_cross: `pref_row_first` under the CLOSE-biased modes reads
     80.33% (static_close, rbl_static) / 84.96% (rbl_dyn). ACT beats COL by the
     mode's definition, so an ACT-ready entry takes the one cycle in tCCD (4 at
     BL8) when the next column becomes eligible: 5-cycle period, 4/5. It was
     100% only while the test poked tCCD=1. Exempted with a 0.75 floor (same
     treatment as in_order). The in_order floor failure (PUMICE-021, 37.87%)
     is unchanged and gains the two close-biased restored modes.
  3. Host: Pumice.set_page_access_cfg / set_page_rbl_cfg (shadowed full-word
     writes, shape BEFORE mode), presets adapt_access / rbl_static / rbl_dyn
     on the reorder config, and RUN_PROFILES["paging"] (modes 4..7 x
     incremental + col_major) as the sim gate for the CSR path.

Results (restored tree):
  * pumice suites (clean-all, run-all-full-parallel): fub 96 / macro 3 /
    top 117 pass, 1 fail = PUMICE-021 (in_order floor, pre-existing).
  * char sim, TEST_CHAR_PROFILE=paging: families + families_x16 pass.
  * 75 MHz post-route, PUMICE_SYS_75=1: WNS +0.020 ns, 0 failing of 72888
    endpoints, LUT 52.9% (33550), worst path unchanged in kind -- the
    arbiter's r_rd_pop -> r_bank pre-pick-to-output register, not the
    predictor tables.

Tier A result (PUMICE_ENHANCED=1, same 75 MHz flow): does NOT close.
  AltSpreadLogic_high: WNS -0.053 ns, TNS -0.221, 8 failing of 72894.
  ExtraTimingOpt:      WNS -0.021 ns, TNS -0.048, 4 failing of 72894.
  Failing endpoints = the cross-CAM global-oldest cone (u_rd_cam/r_older ->
  u_arbiter/r_{rd,wr}_col_q, 16 levels) the arbiter's BASIC/ENHANCED note
  names, plus the base build's own r_*_pop -> r_bank paths that sit within
  +-0.05 ns of zero in every build (placement noise). Tracked as PUMICE-024
  with the candidate fix (register the head compare one stage earlier); the
  overlays stay an env opt-in and the board build is the base tier.

### ORDER MODES IN THE BASE BUILD (2026-09-09): in_order per channel, age_threshold registered

Sean: "full in-order can be a CSR mode on top of FR-FCFS and age should also
work" -- build it, straight to bitstream. The enhanced-tier miss (PUMICE-024)
was entirely the GLOBAL read-vs-write age compare; in_order itself is two
logic levels off the older matrix FR-FCFS already reads. So:

  * in_order (SCHED_POLICY.order_mode=1) is now a BASE-build mode: each CAM
    is masked to its oldest entry and the arbiter's normal read/write
    preference (drain watermarks, round robin, age-boost tiebreak) picks the
    side. Each channel is strictly FIFO; AXI orders nothing between AR and
    AW and the RAW hazard is the CAM snarf's. The global age compare
    (w_rd_head_wins, sch_head_rel export) stays behind +define+PUMICE_ENHANCED
    as "global in_order": with it the younger head waits.
  * age_threshold (order_mode=3) is a BASE-build mode: the CAMs register
    their per-entry age flags (r_age_exceed, cleared on allocation, masked by
    validity) so the 16-bit subtract+compare never enters the arbiter's mask
    cone. A boost engaging a cycle late is a preference, not a guard.
  * Host: Pumice.set_sched_policy (SCHED_POLICY by name), presets inorder
    (order_mode=1) and age_thr (order_mode=3, thresh 8), RUN_PROFILES["order"].
    SCHED_TUNING.force_inorder / lookahead_active are legacy fields the
    rearchitected RTL does not read -- the old "inorder" preset was a no-op on
    the board. Their retirement from the RDL is a follow-up (regen + host).
  * DV: test_pumice_core_sched_order_base runs the parked-victim order sweep
    on the BASE netlist (the enhanced/base builds of one testcase now get
    separate sim_build trees -- sharing one produced a g++ segfault when the
    regression and a standalone run compiled it at once).

75 MHz post-route with the order modes in the base build: -0.046 ns on 4
endpoints (flow placer), -0.085 ns on 12 (ExtraTimingOpt) -- all the
arbiter's own r_*_pop -> r_bank pre-pick path, the +-0.05 ns band seen in
every build today. The -0.046 build is in the tree for the board run;
PUMICE-024 carries the real fix (shorten the pre-pick stage).


### CONFIG CLEANUP (2026-09-09): the CSR map and the host presets match the current architecture

Sean: "clean up the configs so they make sense with the latest arch". Audit
method: every `sw = rw` field in pumice_csr.rdl vs every `hwif_out.<reg>.
<field>` pumice_top.sv actually reads. Dead and now RETIRED (fields become
RSVD, addresses kept so the map does not shift):

  * SCHED_TUNING @0x040, all of it: lookahead_active, force_inorder,
    age_max_runtime, txn_queue_high_water, lookahead_max_obs. They belonged
    to the pre-rearchitecture scheduler; the CAM+arbiter never read them, so
    the host's `inorder` preset and the harness's rd_in_order forwarding
    were silent no-ops on the board. Scheduling is SCHED_POLICY.
  * REFRESH_TUNING.refpb_policy_or / refresh_defer_active / zqcs_freq_hz:
    refresh mode and the JEDEC credits are REF_CTRL @0x140; no ZQCS engine.
    page_policy_or stays (it is the static OPEN/CLOSE override).
  * SCHED_POLICY.auto_precharge_en: AP is the page policy's (static_close and
    the mode 5..7 predictors drive ap_mode_en).
  * PAGE_POLICY_CFG.ctr_width: the adapt_access counter is the paper's 2-bit
    saturating counter, not selectable.
  Left alone (dead but not "config"): INIT_TUNING.zq_retries/init_timeout_ms,
  TIMINGS_CL_CWL_WR.CL/CWL/tRFCpb, the PASR masks -- init/memory-type
  plumbing for another pass.

Host (pumice_char.py): every preset knob is now a CSR the RTL reads.
  levers: scheme (ADDR_MAP), page_policy (static), page_mode (predictors
  4..7), order_mode (0 FR-FCFS / 1 in_order / 3 age_threshold), t_refi,
  refresh (REF_CTRL credits). Removed: reorder (== open_page, FR-FCFS
  reorders by default), lever_lookahead / lever_rdooo (== baseline),
  lever_open (== open_page), LOOKAHEAD_MAX, set_scheduler /
  get_lookahead_max. Added: inorder_open, refresh_credit, profiles
  open_min / refresh; smoke = baseline/bank_interleave/open_page/inorder;
  matrix = + age_thr. set_refresh() now programs REF_CTRL.
  rd_in_order stays as the HARNESS check-engine bit (CTRLR_CFG[24]); it no
  longer touches the controller.
DV: test_pumice_top configure_via_csr / wr_rd_ooo_multi_id and the char
  uart sweep use SCHED_POLICY.order_mode; the host unit test covers
  set_sched_policy + set_refresh(REF_CTRL).

### THE TWO STANDING FAILURES, DIAGNOSED (2026-09-09)

Sean asked whether the two failures I had been calling "pre-existing" were
test issues or RTL bugs. Both are TEST issues, and both were masking
something. Measured, not argued:

1. `pagehit_rate2_x16_free_earlyen` was not failing -- it was XPASSING. It is
   a strict xfail (a negative model: an rddata_en->valid strobe decoupled from
   the data must be SEEN as mismatches), so "FAILED" meant the injected fault
   was no longer detected. That is the dangerous direction, so the first
   question was whether the METRIC had gone blind. It has not. A latency
   sweep settles it:

       a7_read_valid_lat   5   6   7   8   10  12
       result             ok  ok  ok  MISM MISM MISM   (read_latency = 8)

   CORRECTION to the first reading of this: it is not "the design tolerates an
   early strobe". Sweeping the full range gives a 4-cycle BAND --

       valid_lat   0  1  2  3 | 4  5  6  7 | 8  10  12
       result      X  X  X  X | ok ok ok ok| X   X   X

   -- and both edges are physical. Below 4 the strobe precedes the data
   (t_rddata_en=4 + valid_lat against data anchored at read_latency=8: there
   is nothing on the bus yet). At 8 the next pipelined page-hit read has
   already overwritten the held DQ bus. The window is centred exactly where a
   correct PHY contract puts it, and the metric flags everything outside it.
   The late side is NOT recoverable by the read-data realign tap either: the
   full sel 0..15 sweep at valid_lat=10 mismatches at every tap, so those
   points are a genuine misalignment rather than an untrimmed knob. Fix: the
   lat-6 case becomes a positive mid-window test, `_edge` (7) and `_lowedge`
   (4) pin both edges so a window that shifts or narrows fails loudly, and the
   strict-xfail negative model moves to lat 10.

2. PUMICE-021's in_order floor is a MISCALIBRATED FLOOR. Discriminator across
   the eight paging modes under in_order is exact: every mode that drives
   auto-precharge reads 37.87-44.14%, every mode that does not reads exactly
   80.33% / stall=94. A command-cadence probe on the same window gives the
   mechanism:

       static_open  x in_order  89.51%  ops {ACT:8, WR:64}    gaps 4x63, 8x8
       static_close x in_order  36.89%  ops {ACT:26, WRA:26}  gaps 4x25, 8x34

   Non-AP paging activates once and streams columns at tCCD: one command per
   access, gap 4. AP paging makes every access two DEPENDENT commands, ACT
   then column-with-auto-precharge: ACT->col is tRCD (gap 4), col->next ACT is
   the head advancing through the arbiter's 3-stage pick pipeline (gap 8). A
   12-cycle period instead of 4. FR-FCFS fills those gaps from other banks
   (hence 100% in the same windows); strict ordering cannot, by definition.
   The 0.45 floor and its "expected 56.3%" note predate the pipelined arbiter.
   Fix: floors split by mechanism, 0.75 non-AP / 0.30 AP, with the probe
   numbers in the comment and an assertion that the AP modes are present so
   the split cannot cover an empty set. PUMICE-021 closed.

The col->ACT head advance is the one real performance lead here: shortening it
lifts every AP-paging number under strict ordering. It is the same pre-pick
stage that owns the 75 MHz critical path, so it is one change with both
payoffs -- tracked under PUMICE-024, not treated as a defect.

### PRE-PICK OPERAND MUXING (2026-09-09): the ENHANCED tier closes 75 MHz

The order-mode overlays missed 75 MHz by 21-53 ps (PUMICE-024). The overlays
were not the problem. The arbiter's output stage indexed the CAMs' flat
{bank,row,col} vectors with the REGISTERED pre-pick slot, so six
NUM_ENTRIES:1 muxes sat AFTER the pre-pick flop feeding r_bank/r_row/r_col.
That is the path every build reported: `r_*_pop -> ... -> r_bank`.

Fix: mux at the pre-pick flop and register the already-narrow operands per
class. The wide muxes land in the STAGE-1b cycle, where arg_sel has already
resolved and there is slack; the output stage keeps only the class-priority
mux over narrow values. This is not a new idiom -- `rd_col_ap` already
sampled `r_ap_snap[f_bank(..., w_sel_rd_col_s)]` at that same flop. Sampling
a cycle earlier is also more coherent: an entry's key is fixed at insert and
the forward guards stop a just-selected slot being re-selected, so the
operands come from the same epoch as the decision.

Post-route at 75 MHz, same flow:

| Build | Before | After |
|---|---|---|
| base | +0.010 ns, 0 failing | +0.009 ns, 0 failing |
| ENHANCED | -0.021 ns, 4 failing | +0.005 ns, 0 failing of 72896 |

About +144 flops, +0.19% LUT. The base tier was already closing so it does not
move; the enhanced tier closes for the first time, which retires PUMICE-024
and -- with the earlier pipelining work -- PUMICE-017, whose -48.861 ns
premise no longer exists at a HIGHER clock than it was filed against.

What this does NOT fix is the throughput half of the same cone: the
column-to-next-ACT head advance is still 8 cycles, so strict in-order under
the auto-precharge paging modes still pays the pick pipeline twice per access
(PUMICE-021). That is a deeper change than moving a mux.

### ON SILICON (2026-09-10): write target MET at 570 MB/s; read pinned at 48.7% of peak

Nexys A7 210292BFA3EE, 75 MHz / DDR2-300, base-tier bitstream at 3c66f442d.
Peak 600 MB/s. Leveling clean (bitslip 0, tap 4, eye width 10), 32 MB memtest
8/8 chunks 0 dirty, every characterization point integrity-clean.

| Direction | Measured | Target | % peak |
|---|---|---|---|
| Write | 570.0 MB/s | 510 | 95.0% |
| Read  | 291.7 MB/s | 450 | 48.6% |

The same path measured 12.7 MB/s flat in July. Writes are now at the data-path
limit; the whole write-lead block, the JEDEC timings and the paging work land
as intended on hardware.

READ IS A HARD CEILING, and the invariance is the finding. 291.7-292.2 MB/s
and 49.2 cycles latency in every configuration that streams, unchanged by
burst length (bl4 290.8 / bl8 291.7 / bl16 291.7), access pattern, paging mode
or scheduling mode. Identical numbers at bl16 rule out any
transaction-concurrency or Little's-law bound -- more bytes per transaction
would have moved it. So it is a per-cycle rate below the transaction layer.
48.7% of peak against a write path at 95.7% points at a return path moving one
AXI beat every other cycle. Tracked as PUMICE-025, which says to rule out the
harness's read CRC engine FIRST (it is the generator, not the controller) and
explicitly not to tune the scheduler, since every scheduling mode gives the
identical number.

CORRECTION (same day): the first pass reported refresh_credit at 574.0/292.2
as the best config. That was an ARTIFACT of run order. `apply()` only
programmed a mode axis when the preset set one, so a preset leaving page_mode
unset INHERITED the previous config's; refresh_credit is a CLOSE-page preset
that ran after rbl_dyn and inherited its page_mode=7. Standalone it measures
33.8/35.8. apply() now programs every axis on every config, and the re-run is
order-independent and 36/36 integrity-clean. A characterization matrix whose
numbers depend on run order is worthless, and this one silently did.

Mode characterization, row_major BL8, write/read MB/s: open_page / age_thr /
adapt_time / adapt_access / rbl_dyn all 570.0/291.7; rbl_static 33.8/36.9;
inorder, refresh_credit and baseline 33.8/35.8. The split is binary --
page-open reaches 570, page-closed sits at ~34, nothing in between.

Two results worth keeping. **rbl_dyn vindicates the dynamic threshold**:
rbl_static at the same base miss threshold collapses to 33.8 MB/s because it
closes pages under a streaming pattern, while rbl_dyn's per-epoch hill-climb
backs the threshold off and recovers full bandwidth. That is exactly the
situational win the mode work exists to show, and only real traffic shows it.
**age_threshold is free** -- identical to FR-FCFS until it engages -- so it,
not in_order, is the mode to reach for when latency bounding is the goal;
in_order costs 17x on this pattern, matching the sim prediction.
