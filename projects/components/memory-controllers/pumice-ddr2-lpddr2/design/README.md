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
