<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Command Arbiter (`scoria_cmd_arbiter`)

**Module:** `scoria_cmd_arbiter.sv`
**Location:** `rtl/fub/`
**Category:** scheduling / arbitration
**Parent:** `scoria_scheduler_layer`
**Status:** complete and formal-proven (`formal/scoria/cmd_arbiter/scoria_cmd_arbiter.sby`; the `nofix` task runs with `BUG001=0` to prove the rank-global fire-stage re-check matters)

---

## Purpose

The single-issue pick core of the scheduler layer. Each cycle it reads the read and write CAMs as flat per-entry vectors, classifies every entry as column, activate, or precharge, applies the runtime scheduling policy, enforces JEDEC timing through the bank/global timer readiness inputs, and pushes one abstract DRAM command into the scheduler-to-DFI FIFO. `andesite_cmd_arbiter` inherits this mechanism and adds bank-group long/short spacing.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `NUM_RANKS` | int | 1+ | 1 | ranks per channel (v1 is single-rank pick) |
| `NUM_BANKS` | int | 8..16 | 8 | banks per rank |
| `ROW_WIDTH` | int | — | 14 | row address width |
| `COL_WIDTH` | int | — | 10 | column address width |
| `AXI_ID_WIDTH` | int | — | 8 | AXI transaction ID width |
| `NUM_ENTRIES` | int | 8..32 | 8 | read and write CAM depth |
| `AGE_WIDTH` | int | — | 16 | age-counter width |

: Table 2.15.1: Command arbiter parameters

## Interface

### CAM scheduler vectors

| Signal | Direction | Width | Description |
|---|---|---|---|
| `rd_sch_valid_i` | in | `NUM_ENTRIES` | read CAM per-entry valid |
| `rd_sch_bank_i` | in | `NUM_ENTRIES*BKW` | read candidate bank per entry |
| `rd_sch_row_i` | in | `NUM_ENTRIES*ROW_WIDTH` | read candidate row per entry |
| `rd_sch_col_i` | in | `NUM_ENTRIES*COL_WIDTH` | read candidate column per entry |
| `rd_sch_older_i` | in | `NUM_ENTRIES^2` | read CAM age-order matrix |
| `rd_sch_age_exceed_i` | in | `NUM_ENTRIES` | read entry age-boost flag |
| `rd_sch_qos_i` | in | `NUM_ENTRIES*4` | read entry AxQOS value |
| `rd_sch_head_rel_i` | in | `AGE_WIDTH` | read CAM oldest relative age |
| `wr_sch_valid_i` | in | `NUM_ENTRIES` | write CAM per-entry valid |
| `wr_sch_bank_i` | in | `NUM_ENTRIES*BKW` | write candidate bank per entry |
| `wr_sch_row_i` | in | `NUM_ENTRIES*ROW_WIDTH` | write candidate row per entry |
| `wr_sch_col_i` | in | `NUM_ENTRIES*COL_WIDTH` | write candidate column per entry |
| `wr_sch_older_i` | in | `NUM_ENTRIES^2` | write CAM age-order matrix |
| `wr_sch_age_exceed_i` | in | `NUM_ENTRIES` | write entry age-boost flag |
| `wr_sch_qos_i` | in | `NUM_ENTRIES*4` | write entry AxQOS value |
| `wr_sch_head_rel_i` | in | `AGE_WIDTH` | write CAM oldest relative age |
| `wr_commit_ready_i` | in | 1 | write CAM drain-FIFO has room |
| `wr_commit_valid_o` | out | 1 | write CAM entry committed this cycle |
| `wr_commit_slot_o` | out | `PTRW` | committed write CAM slot |
| `rd_issue_ready_i` | in | 1 | read CAM issue-FIFO has room |
| `rd_issue_valid_o` | out | 1 | read CAM entry issued this cycle |
| `rd_issue_slot_o` | out | `PTRW` | issued read CAM slot |

: Table 2.15.2: CAM scheduler vector ports

### Policy CSRs and QoS inputs

| Signal | Direction | Width | Description |
|---|---|---|---|
| `sched_order_mode_i` | in | 2 | `0/2` FR-FCFS, `1` in_order, `3` age_threshold |
| `sched_row_sel_i` | in | 2 | activate select: `0` oldest, `1` most_pending, `2` fewest_pending |
| `sched_col_sel_i` | in | 2 | column select: `0` oldest, `1` most_pending, `2` fewest_pending |
| `sched_access_pref_i` | in | 2 | `0/1` column_first, `2` row_first, `3` precharge_first |
| `sched_wr_high_wm_i` | in | 8 | write-batching drain arm threshold |
| `sched_wr_batch_max_i` | in | 8 | maximum consecutive write columns per drain; `0` = unbounded |
| `sched_wr_low_wm_i` | in | 8 | write-batching drain disarm threshold |
| `sched_prio_sub_i` | in | 2 | `0/2` load_over_store, `1` none, `3` age_boost |
| `sched_qos_en_i` | in | 1 | narrow each class to max-AxQOS candidates |

: Table 2.15.3: Scheduling policy CSR ports

### Page-policy inputs

| Signal | Direction | Width | Description |
|---|---|---|---|
| `page_policy_i` | in | `page_policy_e` | legacy OPEN / CLOSE policy |
| `ap_mode_en_i` | in | 1 | runtime page-policy engine override enable |
| `ap_close_i` | in | `NUM_BANKS` | per-bank auto-precharge close mask |
| `timeout_pre_req_i` | in | 1 | idle-expired bank requests background precharge |
| `timeout_pre_bank_i` | in | `BKW` | idle-expired bank index |

: Table 2.15.4: Page-policy input ports

### Timer readiness

| Signal | Direction | Width | Description |
|---|---|---|---|
| `bank_act_ready_i` | in | `NUM_RANKS x NUM_BANKS` | per-bank activate ready |
| `bank_rdwr_ready_i` | in | `NUM_RANKS x NUM_BANKS` | per-bank read/write ready |
| `bank_pre_ready_i` | in | `NUM_RANKS x NUM_BANKS` | per-bank precharge ready |
| `bank_act_ready_la_i` | in | `NUM_RANKS x NUM_BANKS` | advisory lookahead activate ready |
| `bank_rdwr_ready_la_i` | in | `NUM_RANKS x NUM_BANKS` | advisory lookahead read/write ready |
| `bank_pre_ready_la_i` | in | `NUM_RANKS x NUM_BANKS` | advisory lookahead precharge ready |
| `bank_row_active_i` | in | `NUM_RANKS x NUM_BANKS` | per-bank row-active flag |
| `bank_open_row_i` | in | `NUM_RANKS x NUM_BANKS x ROW_WIDTH` | per-bank open row |
| `tfaw_ok_i` | in | `NUM_RANKS` | per-rank tFAW window ok |
| `trrd_ok_i` | in | `NUM_RANKS` | per-rank tRRD spacing ok |
| `twtr_ok_i` | in | 1 | write-to-read turnaround ok |
| `trtw_ok_i` | in | 1 | read-to-write turnaround ok |
| `tccd_ok_i` | in | 1 | column-to-column spacing ok |
| `t_ccd_i` | in | 8 | tCCD in controller-clock cycles |

: Table 2.15.5: Timer readiness ports

### Maintenance request/grant

| Signal | Direction | Width | Description |
|---|---|---|---|
| `refresh_req_i` | in | 1 | refresh controller wants the bus |
| `refresh_drain_i` | in | 1 | refresh drain burst in progress |
| `refresh_kind_i` | in | 1 | `0` all-bank `REF`, `1` per-bank `REFpb` |
| `refresh_bank_i` | in | `BKW` | `REFpb` rotor bank mirror |
| `refresh_grant_o` | out | 1 | bus granted to refresh |
| `t_rfc_i` | in | 16 | tRFC / tRFCab recovery |
| `t_rfc_pb_i` | in | 8 | tRFCpb recovery; `0` falls back to `t_rfc_i` |
| `zq_req_i` | in | 1 | ZQ calibration controller wants the bus |
| `zq_grant_o` | out | 1 | bus granted to ZQ |
| `t_zqcs_i` | in | 16 | tZQCS block window |

: Table 2.15.6: Maintenance request/grant ports

### Init passthrough

| Signal | Direction | Width | Description |
|---|---|---|---|
| `init_done_i` | in | 1 | initialization complete; host commands admitted when high |
| `init_cmd_valid_i` | in | 1 | init sequencer has a command |
| `init_cmd_op_i` | in | `dram_op_e` | init command opcode |
| `init_cmd_bank_i` | in | `BKW` | init command bank |
| `init_cmd_row_i` | in | `ROW_WIDTH` | init command row |

: Table 2.15.7: Init passthrough ports

### Event strobes

| Signal | Direction | Width | Description |
|---|---|---|---|
| `evt_act_o` | out | 1 | activate fired |
| `evt_rd_o` | out | 1 | read column fired |
| `evt_wr_o` | out | 1 | write column fired |
| `evt_pre_o` | out | 1 | precharge fired |
| `evt_ap_o` | out | 1 | auto-precharge bit of fired column |
| `evt_rank_o` | out | `RKW` | fired command rank |
| `evt_bank_o` | out | `BKW` | fired command bank |
| `evt_row_o` | out | `ROW_WIDTH` | fired command row |

: Table 2.15.8: Timer event-strobe ports

### Command output

| Signal | Direction | Width | Description |
|---|---|---|---|
| `cmd_valid_o` | out | 1 | command valid to scheduler-to-DFI FIFO |
| `cmd_ready_i` | in | 1 | FIFO can accept command |
| `cmd_op_o` | out | `dram_op_e` | abstract DRAM opcode |
| `cmd_rank_o` | out | `RKW` | rank |
| `cmd_bank_o` | out | `BKW` | bank |
| `cmd_row_o` | out | `ROW_WIDTH` | row |
| `cmd_col_o` | out | `COL_WIDTH` | column |
| `cmd_ap_o` | out | 1 | auto-precharge flag |

: Table 2.15.9: Command output ports

### Stall attribution

| Signal | Direction | Width | Description |
|---|---|---|---|
| `stall_bp_o` | out | 32 | DFI FIFO backpressure |
| `stall_refresh_o` | out | 32 | refresh owns the bus |
| `stall_zq_o` | out | 32 | ZQ request or tZQCS block |
| `stall_noreq_o` | out | 32 | no CAM entry pending |
| `stall_turnaround_o` | out | 32 | tWTR / tRTW |
| `stall_tccd_o` | out | 32 | tCCD spacing |
| `stall_actlimit_o` | out | 32 | tFAW / tRRD |
| `stall_banktimer_o` | out | 32 | per-bank tRCD / tRP / tRAS |

: Table 2.15.10: Stall-attribution ports

## Microarchitecture internals

### Classification

Every valid read and write CAM entry is classified independently against the registered bank image:

- **Column** — the entry's bank is row-active and its row matches the open row.
- **Activate** — the bank is idle (no row open).
- **Precharge** — the bank is row-active but the entry's row does not match.

The three masks are mutually exclusive per entry. Column eligibility also requires `rd_issue_ready_i` or `wr_commit_ready_i` so a fired column never outruns the CAM retire/drain path.

### Priority chain

The per-cycle pick is a fixed priority chain. Maintenance and init outrank all demand traffic; demand class ordering is selected by `sched_access_pref_i`.

```text
if !init_done:
    init passthrough
else if w_zq_busy:
    idle (tZQCS block)
else if refresh_req or refresh_drain:
    if REFpb and rotor bank active: precharge rotor bank
    else if REFpb and rotor bank idle and refpb_safe: REFpb + grant
    else if any bank active: precharge lowest active ready bank
    else if ref_safe: REF + grant
else if zq_req:
    if any bank active: precharge lowest active ready bank
    else if zq_safe: ZQCS + grant
else:
    choose demand class by access_pref
    column -> read first unless write-batching / policy override
    activate -> bank-parallel oldest ready
    precharge -> wrong-row oldest ready
    timeout precharge -> lowest priority
```

: Table 2.15.11: Priority chain

### Policy CSRs

`sched_order_mode_i` narrows the class masks without changing the branch chain:

- `0/2` — FR-FCFS (default).
- `1` — `in_order`: only the oldest entry in each CAM is eligible; global age order is available under `PUMICE_ENHANCED`.
- `3` — `age_threshold`: when any entry is age-boosted, every class narrows to boosted entries.

`sched_prio_sub_i` selects read/write ordering within a class:

- `0/2` — `load_over_store`: reads first (default).
- `1` — `none`: fair alternation on `r_dir_rr`.
- `3` — `age_boost`: reads first unless the write-class winner is boosted and the read-class winner is not.

`sched_row_sel_i` and `sched_col_sel_i` choose among column/activate candidates by oldest, most pending, or fewest pending, with age as tie-break. When `sched_qos_en_i` is set, each class is first narrowed to the maximum AxQOS value before the population/age select runs.

### Write-batching hysteresis

`r_wr_drain` arms when write CAM occupancy reaches `sched_wr_high_wm_i` and disarms only when occupancy falls to `sched_wr_low_wm_i`. While armed, writes outrank reads in every demand class. `sched_wr_batch_max_i` bounds the drain: after that many write columns the drain yields until a read column fires, preventing unbounded read starvation. `sched_wr_high_wm_i == 0` disables batching entirely.

### Pick pipeline

The pick pipeline was deliberately deepened by one stage (PUMICE-018) to close double-issue paths opened by the STAGE-1a snapshot register:

- **STAGE-1a** — snapshot the qualified class masks, age-order matrices, population arrays, and per-bank auto-precharge verdict into a coherent epoch.
- **STAGE-1b** — run the per-class `arg_sel` / `arg_oldest` on the snapshot.
- **pre-pick flop** — latch the selected slot and pre-mux the wide `{bank,row,col}` operands off the output-stage critical path.
- **output register** — hold the final command and retire it when the FIFO accepts.

The pipeline advances with `w_out_ready`, so it stalls coherently under FIFO backpressure. Because the snapshot and pre-pick registers create a 3–4 cycle window before the CAM `sch_valid` drop and bank timers reflect a pick, `w_if_preact_sel/pre/out` and `w_if_col_sel/pre/out` guard against the same slot or bank being re-selected while a command is mid-pipeline.

### Final safety gate

`w_out_safe` re-checks the registered pick against live bank timers, rank-global windows, turnaround/tCCD live terms, and `!w_zq_busy`. Unsafe picks are **dropped**, not held: the CAM entry remains valid and is re-picked later. The command push is `cmd_valid_o = r_pick_valid && w_out_safe`, which is the BUG-003 fix; previously an unsafe pick could still push into the FIFO because `cmd_valid_o` was `r_pick_valid` unconditionally.

### Fire-stage bug fixes

BUG-001 adds `tfaw_ok_i[RK0] && trrd_ok_i[RK0]` to the ACT case of `w_out_safe` because per-bank timers cannot see rank-global windows; an ACT already in the pipeline when tFAW/tRRD closed would otherwise issue. The STAGE-1b live ACT gate also squashes activate classes while the windows are closed, and the final gate catches any remaining race.

BUG-002 adds `!w_zq_busy` to `w_out_safe`. `w_zq_busy` loads on the accepted fire of a ZQCS, so during the ZQCS fire cycle the pick cone still sees it low and freely selects a follow-on command; the fire-stage re-check prevents that command from issuing inside the calibration window.

### Column spacing and turnaround guards

`tccd_ok_i` reloads on the column fire, 3–4 pick-pipeline cycles after classification. The forward counter `r_tccd_fwd` reloads on column selection and blocks new column classifications while it is above one or while another column is being selected with `t_ccd_i > 1`, replacing the stale flopped `tccd_ok_i` without adding a full tCCD bubble.

The global turnaround `ok` flags are flopped and drop two cycles after a fired column. `r_wrfire0/1` and `r_rdfire0/1` block cross-direction column picks for two cycles, but they load on the cycle after fire while the pick is evaluated the cycle before its own command leaves, leaving a one-cycle blind spot. The live terms `!(w_fire_out && r_do_wr)` and `!(w_fire_out && r_do_rd)` close that seam.

### Auto-precharge guard

Under close-page or per-bank `ap_close_i`, a fired read/write with auto-precharge closes the bank. `r_apguard0/1` block same-bank columns for two cycles, and `r_ap_closing` is held until `bank_row_active` drops.

### Refresh safety

`w_ref_safe` requires no possibly-open row, no in-flight precharges, clear guard registers, `!w_rfc_busy`, `!r_grant`, and `!r_zq_grant`. The `!r_grant` term prevents a double-REF when `refresh_req` drops one cycle late. `w_refpb_safe` requires only the rotor bank to be closed; other banks continue serving row hits. While a refresh is pending, columns to banks the refresh will close are masked (`w_ref_col_block`) so the refresh drain cannot livelock behind an in-flight column guard.

### tRFC recovery and tZQCS block

`r_rfc_cnt` loads on a fired REF; while nonzero it blocks further activates and refreshes. `REFpb` uses `t_rfc_pb_i` if non-zero, otherwise `t_rfc_i`. `r_zqcs_cnt` loads on a fired ZQCS and blocks all command issue while nonzero. The two counters are keyed separately (`r_grant` for refresh, `r_zq_grant` for ZQ) so the two maintenance windows do not corrupt each other.

### Stall attribution

Stall buckets are mutually exclusive and ordered so their deltas sum to the total stalled-cycle count. Priority order is: `w_out_reject` → `stall_banktimer`; else a picked command waiting on `cmd_ready_i` → `stall_bp`; else `w_zq_busy`/`zq_req` → `stall_zq`; else `refresh_req`/`refresh_drain` → `stall_refresh`; else no CAM entry → `stall_noreq`; else `!twtr_ok`/`!trtw_ok` → `stall_turnaround`; else `!tccd_ok` → `stall_tccd`; else `!tfaw_ok`/`!trrd_ok` → `stall_actlimit`; else `stall_banktimer`.

: Table 2.15.12: Stall attribution priority

### Maintenance request/grant semantics and event strobes

The arbiter keeps two inherited request/grant pairs — one for refresh and one for ZQ — rather than a single unified `maint_req`/`maint_tag` channel. The unified tagged channel remains the conceptual model; the formatter-side maintenance encoding derives from it downstream. The family doctrine applies: **request and wait, never preempt**. A maintenance source raises its `req` and holds it until `grant` arrives; it cannot yank the bus away from an in-flight host command.

On a safe fire (`w_fire_out`), `evt_act_o`, `evt_rd_o`, `evt_wr_o`, and `evt_pre_o` strobe the bank and global timers; `evt_rank_o`, `evt_bank_o`, and `evt_row_o` carry rank, bank, and row. `evt_ap_o` is `r_ap_out` and does not gate on fire.

## FSM policy

The arbiter is priority logic plus pipeline registers, not an FSM. The "state" is the CAM contents, the timer inputs, and the pipeline registers; there is no explicit state machine governing the pick. The policy is selected by runtime CSRs and recombined every cycle.

## Timing

The arbiter issues at most one grant per cycle. The critical path runs from CAM valid/row inputs through classification, the STAGE-1a snapshot, the STAGE-1b argmax, the pre-pick flop, and the final live safety gate to the FIFO push. The output-stage data muxes were moved into the pre-pick flop to keep the final stage small.

## Notes

- **Dropped, not held:** `w_out_reject` discards an unsafe registered pick rather than holding it. Holding head-of-line blocks the pipeline behind one bank and was measured as a throughput regression; dropping is safe because every CAM commit/issue is qualified by `w_fire_out` and the entry remains schedulable.
- **Refresh grant hazard:** The `!r_grant` term on `w_ref_safe` prevents a second REF being picked while the first is still in the output register. This is especially dangerous for `REFpb`, because every command advances the device's internal bank rotor.
- **AP verdict snapshot:** `r_ap_snap` captures the per-bank auto-precharge verdict with the STAGE-1a masks. Deciding RD vs. RDA at the output stage would let a column see an `ap_close_i[b]` change and issue a row-stay-open command behind one that closed the same row.
- **ISSUE-002:** Under `row_first` (`sched_access_pref_i == 2`), ACT classification is still gated by `w_act_classify_gate`; under `column_first` activate candidates flow through the pipeline while tFAW/tRRD are closed. This preserves `row_first`'s measured throughput floor.
- **Formal path:** The landed SBY file is `formal/scoria/cmd_arbiter/scoria_cmd_arbiter.sby`, not `formal/scoria/scoria_cmd_arbiter.sby`; the `nofix` task sets `BUG001=0` and fails, proving the rank-global fire-stage re-check is load-bearing.
