# pumice ideal scheduler / datapath — spec-first design

**Status:** design spec (2026-09-07). This directory defines the *ideal* command
and data-path signalling **before** the RTL, so the rewrite targets a spec rather
than patching the current design. Two kinds of artifact:

- `kmaps/` — K-map / truth-table workbooks (`gen_kmaps.py`) for the control logic.
- `waves/` — WaveJSON timing diagrams (`gen_waves.py`) for the ideal cadence.
  Render at <https://wavedrom.com/editor.html> or `npx wavedrom-cli -i f.json -s f.svg`.

Regenerate: `python3 gen_kmaps.py && python3 gen_waves.py`.

DDR2-300 @ aclk 75 MHz, DFI_RATE=2, BL4. Peak = **600 MB/s** (8 B/cycle). Pumice
today: **~90 MB/s (15 %)**. LiteDRAM on this exact board: ~500 MB/s (~85 %). The
whole point of this spec is to close that gap.

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
   → `kmaps/pumice_cmd_path_kmap.xlsx` (CMD_DECISION, FORWARD_STATE),
     `waves/07`, `waves/08`.
2. **Tag-based, recoverable returns** — match DFI returns to reads by slot/id,
   not issue-FIFO position; add a per-read length watchdog so a short/lost burst
   can't wedge the AR-order drain. Return depth D ≥ ⌈(t_rddata_en+CL)/tCCD⌉ = 5,
   so the pipe stays full across the read round-trip.
   → `kmaps/pumice_data_path_kmap.xlsx` (RD_RETURN, RETURN_TAGGING),
     `waves/01`, `waves/08`.
3. **Decouple read/write issue** — split the DFI command FIFO into read/write
   lanes (or let a WR bypass a RD stalled only on `rd_op_ready_i`), so a read
   stall can never be reported as a write wedge.
   → `kmaps/pumice_cmd_path_kmap.xlsx` (CMD_DECISION notes), `waves/09`.

Target: same-bank open-page streaming at **~tCCD rate** (waves/01, waves/02),
cross-bank ACT pipelining (waves/04), i.e. ~500–600 MB/s.

## Artifact index

| file | defines |
|------|---------|
| `kmaps/pumice_cmd_path_kmap.xlsx` | FR-FCFS command decision, AP/page-policy, timing-gate legend, forward-state |
| `kmaps/pumice_data_path_kmap.xlsx` | wr drain, B-gating, rd return, per-bank outstanding tracker, return tagging |
| `waves/01_open_read_stream` | ideal RD stream @ tCCD — the throughput target |
| `waves/02_open_write_stream` | ideal WR stream @ tCCD |
| `waves/03_page_miss_act_rd` | ACT→tRCD→RD first-access latency |
| `waves/04_bank_parallel_act` | cross-bank ACT pipelining (tRRD/tFAW) |
| `waves/05_page_conflict_pre_act_rd` | PRE→tRP→ACT→tRCD→RD |
| `waves/06_refresh_insertion` | PREA→REF→tRFC→resume |
| `waves/07_pick_pipeline_ideal` | pipeline = latency, not rate (the correction) |
| `waves/08_same_bank_outstanding_fix` | ≥2 same-bank columns in flight, forward-state + tagged return |
| `waves/09_failure_stale_image_wedge` | the CURRENT failure chain (reference: what NOT to do) |
| `kmaps/pumice_write_path_kmap.xlsx` | **write drain/commit detail**: DRAIN_HANDSHAKE, CM_RD_STALL_CANDIDATES (why the DFI stops accepting writes -- the same-bank-WR wedge), SERIALIZER_OWED, B_CONSOLIDATION |
| `waves/10_write_drain_pipeline_ideal` | ideal write drain (2 same-bank WR pipelined, no stall) |
| `waves/11_write_same_bank_wedge_ref` | the current write-path wedge (reference; drain FIFO fills, commit_ready drops) |


## Correction (2026-09-07): the wedge is in the WRITE PATH, not the arbiter

Four fixes targeting the arbiter -- including the full correct-by-construction
shadow bank-state (design/kmaps FORWARD_STATE) -- all wedge IDENTICALLY at
`gen_wr_done` in the WRITE-ONLY phase. A fundamental arbiter redesign failing the
same way proves the wedge is downstream: the **write drain/commit path** when
same-bank WR columns pipeline. The write-path spec above (`pumice_write_path_kmap`
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
`pumice_write_path_kmap` -- not the arbiter column mask and not the CAM depth.

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
change (design/kmaps FORWARD_STATE, waves 07/08), timing-critical, board-validated.

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
