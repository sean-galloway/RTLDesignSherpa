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

# Command Arbiter (`pumice_cmd_arbiter`)

**Module:** `pumice_cmd_arbiter.sv`
**Location:** `rtl/fub/`
**Category:** FUB (the pick core)
**Parent:** `pumice_mem_cmd_scheduler`
**Status:** Implemented (single-issue, single-rank v1)

> **Rearchitected:** the SWAG `scheduler.sv` was a multi-mask priority-encoder
> pipeline (Stages 1–4) over a wide `txn_queue` snapshot with a column-op FSM
> (S_NEED_PRE → S_NEED_ACT → S_NEED_RDWR → S_DONE) and a round-robin W/R toggle.
> That block is retired. The live pick core is `pumice_cmd_arbiter` — a
> **combinational, single-issue, FSM-free** priority picker that reads the CAM
> lookup/oldest ports and the per-bank / global readiness inputs and emits ONE
> abstract DRAM command per cycle. It is instantiated inside
> `pumice_mem_cmd_scheduler` alongside the timers, refresh, init, and
> mode-register (see [ch02/19](19_global_timers.md), [ch02/09](09_bank_machine.md),
> [ch02/11](11_refresh_mgr.md), [ch02/12](12_init_engine.md)).

---

## Purpose

`pumice_cmd_arbiter` picks one abstract DRAM command each cycle and pushes it into
the scheduler → DFI command interface. It is PHY/nphases-agnostic and
single-issue; JEDEC timing is enforced by the per-bank (`pumice_bank_timers`) and
global (`global_timers`) readiness inputs it consumes. Open-page vs auto-precharge
is decided **inline** from `page_policy_i` — there is no standalone page
runtime page-policy engine (see [ch02/08](08_page_policy.md)).

The wider `pumice_mem_cmd_scheduler` wrapper wires the arbiter to those timers,
the refresh controller, the init sequencer + mode-register shadow, and an output
command FIFO; the CAM sched-lookup / oldest / commit / issue ports pass through to
`pumice_axi4_ifc`.

## Priority (each cycle)

The pick is a single combinational `if/else` cascade producing an abstract
command plus its side-effects (event strobes, CAM commit/issue, refresh grant),
all gated on the command sink accepting the push:

1. **INIT** (`!init_done_i`) — forward the `init_sequencer` command verbatim
   (`init_cmd_op/bank/row`).
2. **REFRESH** (`refresh_req_i || refresh_drain_i`) — if any bank is active,
   precharge the lowest active, precharge-ready, un-guarded bank (one/cycle); once
   no bank is active, issue `OP_REF` and assert `refresh_grant_o`. The REF fires
   only under **`w_ref_safe`**: the registered view shows every row closed AND no
   row-affecting command is in flight or inside its 2-cycle guard window AND the
   previous REF's tRFC recovery has elapsed. The registered bank view alone is
   2-3 cycles stale, which let a REFab collide with a just-issued ACT (no PRE) —
   silicon-confirmed as refresh-rate-correlated row corruption. **Mission-mode
   tRFC** (`TIMINGS_RFC_REFI.tRFC` -> `t_rfc_i`) is enforced by an arbiter
   down-counter loaded on each fired REF; while non-zero, ACT picks and further
   REFs are blocked (init-time refreshes use `INIT_TIMING1.t_rfc_wait`
   separately). Column picks also carry a **PRE-only 3-cycle bank guard**
   (`w_pre_col_guard`): without it a conflict-PRE could fire in a
   column-readiness gap and a column then pick against the stale
   row-open image (up to 3 cycles end-to-end) — the RD lands on the just-closed row, its data never
   returns, and the rd reorder CAM's AR-order drain wedges behind it
   forever (found by the parked-victim pattern; latent since the
   bank-parallel refactor; PRE-only because the general `w_guarded` also
   covers RD/WR fires and would throttle same-bank column streaming).
   The `SCHED_POLICY.order_mode` overlay (Axis 1) NARROWS the FR-FCFS
   class masks before the pick: `1 in_order` keeps only the head-of-CAM
   entry of the older CAM (relative-age compare across CAMs); `3
   age_threshold` narrows every class to aged entries whenever any exist
   (per-entry 1-bit flags from the CAMs at `SCHED_POLICY.age_thresh`).
   `SCHED_POLICY.prio_sub` selects the read-vs-write key WITHIN a class:
   0/2 load_over_store (default), 1 none (alternating direction toggle,
   flipped on each fired demand op), 3 age_boost (an age-boosted write
   winner outranks a non-boosted read winner — the `age_thresh` flags
   feed this directly).
   `SCHED_WR_WM` write batching: wr-CAM occupancy >= high_wm arms a
   registered drain in which WRITES outrank reads in every demand class,
   released at <= low_wm (high_wm = 0 disables — the default
   read-priority is bit-identical).
   `SCHED_POLICY.access_pref` reorders the demand-CLASS preference itself
   (0/1 column_first = the legacy order, 2 row_first, 3 precharge_first);
   the class is chosen from the possibly-narrowed per-class picks, then
   read-over-write applies within it.
   `SCHED_POLICY.row_sel/col_sel` further steer the SELECTION within the
   (possibly narrowed) activate/column classes: population-first
   (most/fewest schedulable entries sharing the candidate's {bank,row},
   an 8x8 match triangle per CAM) with oldest tie-break; 0 = pure oldest,
   and precharge picks are always oldest.
   `w_ref_safe` also carries **`!r_grant`**: the grant-to-
   request-drop round trip is 2 cycles, so without it the branch re-picked a
   SECOND REF while the first still sat in the output register and the
   refresh DOUBLE-ISSUED on the wire — a silent tRFC-between-REFs violation
   for REFab (present in every build before 2026-08-26), fatal for REFpb
   (each command advances the device's bank rotor). With `refresh_kind_i`
   set (REFpb, LPDDR2 `REF_CTRL.mode=2`) the branch instead precharges ONLY
   the device's rotor bank (`refresh_bank_i`, the controller's mirror of the
   device-internal counter) and issues `OP_REFPB` under `w_refpb_safe`
   (same terms, rotor-bank-scoped row check); the recovery counter loads
   `trfc_pb` instead of tRFCab, and the rank-wide ACT block during that
   (shorter) window also provides the JEDEC spacing between consecutive
   REFpb commands. The sequencing is audited by
   `rtl/fub/pumice_cmd_history_checker.sv` (generate-gated by `CMD_HISTORY_EN`
   inside the scheduler macro, `$fatal` on violation).
3. **COLUMN row-hit** — an issuable RD/WR to an open row.
   **READ-PRIORITY**: a ready read wins over a ready write. Within each
   direction, **oldest** (max CAM relative age) wins the tie-break.
4. **FALLBACK** — no ready row-hit: `ACT` the oldest pending op's row on an idle,
   act-ready, un-guarded bank; or `PRE` a bank that is open on the wrong row.

### Column issuability

For each bank `j` the arbiter drives the CAM lookups with `{bank j, that bank's
open row}` (`bank_open_row_i`), gated valid by `bank_row_active_i`. A returned hit
is issuable when:

- **RD**: `rd_lu_hit && bank_rdwr_ready && tccd_ok && twtr_ok`
- **WR**: `wr_lu_hit && bank_rdwr_ready && tccd_ok && trtw_ok`

The oldest issuable RD (max `rd_lu_age`) and oldest issuable WR are scanned in
parallel across all `N_LU = NUM_BANKS` lookups; read-priority then selects RD over
WR if both exist.

### Auto-precharge (inline page policy)

```
w_ap = (page_policy_i == PAGE_POLICY_CLOSE);
```

A column op becomes `OP_RDA` / `OP_WRA` when the auto-precharge decision is
set, else `OP_RD` / `OP_WR`; `evt_ap_o` tells the bank timers to model the
auto-precharge. The decision is the legacy flat `w_ap`
(`page_policy_i == CLOSE`) unless the runtime page-policy engine is active,
in which case it is per-bank (`ap_close[bank]`) and the engine may also
request idle-timeout closes as the arbiter's lowest-priority pick — see
[ch02/08](08_page_policy.md). (`PAGE_POLICY_HAPPY_HYBRID` was retired
2026-08-25; the enum encoding maps to build default.)

## Per-bank ACT/PRE re-issue guard

Because `pumice_bank_timers` register their readiness outputs (a 2-cycle latency
from an `evt` to `act/pre_ready` dropping), a purely combinational arbiter would
re-issue ACT/PRE to the same bank before the timers reflect it. The arbiter keeps
a **2-cycle per-bank guard** (`r_guard0`, `r_guard1`; `w_guarded = guard0 |
guard1`) set on any accepted **ACT, PRE or column**, and skips guarded banks in
the refresh-PRE and fallback paths. Columns are included because a column fired
<2 cycles ago has not yet dropped the bank's registered `pre_ready` (tRTP/tWR
load), so an unguarded PRE — normal or refresh-drain — could precharge on stale
readiness.

Column ops still need no guard **against each other**: both CAMs exclude a
just-committed/issued slot from their lookup/oldest ports the next cycle
(`r_sched` on the write side, `r_issued` on the read side), so the arbiter never
re-issues the same slot. The shared-DQ-bus
occupancy (a BL burst owns the DQ bus for `BL/DFI_RATE` dfi cycles) is a
`dfi_clk`-domain constraint enforced **downstream** in `pumice_dfi_cmd_path`
(`COL_BURST_CYC`), not here — the CDC decouples `aclk` command issue from
`dfi_clk` DQ timing.

## Interface (arbiter)

| Group                     | Direction | Notes                                                        |
|---------------------------|-----------|--------------------------------------------------------------|
| `page_policy_i`           | in        | OPEN / CLOSE / HAPPY_HYBRID (HAPPY == OPEN in v1)            |
| init passthrough          | in        | `init_done_i`, `init_cmd_{valid,op,bank,row}_i`             |
| refresh                   | in/out    | `refresh_req_i`, `refresh_drain_i`, `refresh_grant_o`       |
| per-bank readiness        | in        | `bank_{act,rdwr,pre}_ready_i`, `bank_row_active_i`, `bank_open_row_i` (`[NUM_RANKS][NUM_BANKS]`) |
| global readiness          | in        | `tfaw_ok_i`, `trrd_ok_i` (per-rank), `twtr_ok_i`, `trtw_ok_i`, `tccd_ok_i` |
| wr CAM lookup + oldest + commit | in/out | `wr_lu_*` (drive + read), `wr_oldest_*`, `wr_commit_{valid,slot}_o` |
| rd CAM lookup + oldest + issue  | in/out | `rd_lu_*`, `rd_oldest_*`, `rd_issue_{valid,slot}_o`         |
| event strobes             | out       | `evt_{act,rd,wr,pre,ap}_o`, `evt_{rank,bank,row}_o` (to timers) |
| command push              | out/in    | `cmd_{valid,op,rank,bank,row,col,ap}_o`, `cmd_ready_i`      |

## Side-effects (all gated on `w_fire = w_valid && cmd_ready_i`)

- `evt_act/rd/wr/pre_o` — strobe the bank + global timers on an accepted issue.
- `wr_commit_valid_o` / `wr_commit_slot_o` — on an accepted WR/WRA, mark the wr
  CAM slot scheduled (enqueue to its drain FIFO).
- `rd_issue_valid_o` / `rd_issue_slot_o` — on an accepted RD/RDA, mark the rd CAM
  slot issued (enqueue to its issue FIFO).
- `refresh_grant_o` — on an accepted `OP_REF`.

`cmd_valid_o` is asserted whenever a command is picked; `cmd_rank_o` is tied to
rank 0 (`RK0`) — v1 is a single-rank pick.

## v1 scope / TODO

- **Single-rank** pick (`RK0 = 0`); multi-rank arbitration is a TODO.
- **HAPPY_HYBRID == OPEN**; the per-bank page predictor is not in the build.
- Write-drain watermark and powerdown are TODO.
- Unused CAM buses (`wr_lu_id_i`, `rd_lu_id_i`, `*_oldest_slot_i`) are absorbed by
  an explicit `unused` sink.

## `pumice_mem_cmd_scheduler` wrapper

The macro instantiates, on a single `aclk`:

| Instance          | Module               | Role                                              |
|-------------------|----------------------|---------------------------------------------------|
| `u_init`          | `init_sequencer`     | JEDEC MRS init; gates traffic until `init_done`   |
| `u_mode_reg`      | `mode_register`      | MRS-updated CL/CWL/BL shadow → `cl_o/cwl_o/bl_o`  |
| `u_refresh`       | `refresh_ctrl`       | tREFI + postpone; enabled after init              |
| `u_bank_timers`   | `pumice_bank_timers` | per-(rank,bank) safe timers + open-row            |
| `u_global_timers` | `global_timers`      | tFAW/tRRD (per-rank), tWTR/tRTW/tCCD (global)     |
| `u_arbiter`       | `pumice_cmd_arbiter` | the pick core (above)                             |
| `u_cmd_fifo`      | `gaxi_fifo_sync`     | output command FIFO, packs `{op,rank,bank,row,col,ap}` (`CMD_W = 4 + RKW + BKW + ROW_WIDTH + COL_WIDTH + 1`, depth `CMD_FIFO_DEPTH=8`) |

The arbiter pushes into `u_cmd_fifo`; the FIFO read side is the macro's
`cmd_*_o` command stream to the DFI layer. `busy_o` is
`!init_done || refresh_req || cmd-fifo-non-empty || any-bank-active`.

Issue rate is **one command per `aclk`**. The arbiter never sees the DFI
multi-phase dimension — the DFI layer packs phases downstream. Selection is
oldest-first by wrap-safe CAM age; there is no QoS, no lookahead window, and no
`SCHEDULER_MODE` OOO/INORDER synthesis switch.
