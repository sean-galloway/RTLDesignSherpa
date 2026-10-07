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

# Core Signal Contracts

## What a contract is here

A signal contract in this repo is a machine-checkable statement of what a signal is allowed to do: a term list with its defining RTL citation, the invariants between terms, and a decision table whose forbidden rows are marked `ILLEGAL`. The canonical methodology is `vault/handbook/design/signal-contracts-and-kmaps.md`; the shared generator machinery is `bin/kmaps/`. A future scoria kmap book will build its contract sheets from the anchors this chapter names.

## Post-RTL citation posture

This MAS is written after the RTL, so every contract below cites the RTL file and a named fence, assertion, or state list rather than a pre-RTL MAS page. When the kmap generator lands, its citation gate will diff the workbook against these anchors; a drift fails the run. The anchor map gives the contract domain, the RTL anchor, the formal suite where one exists, and the current verdict.

| Contract domain | RTL anchor | Formal suite | Verdict |
|---|---|---|---|
| Address decode | `scoria_addr_mapper.sv` — `{rank,bank,row,col}` decode | `scoria_addr_mapper.sby` | PROVEN |
| DDR3 command decode | `scoria_dfi_cmd_formatter.sv` — DDR3 truth-table fence | none | RTL fence |
| LPDDR3 CA encoding | `scoria_dfi_cmd_formatter.sv` — JESD209-2F Table 60 CA-bus block | none | RTL fence |
| Maintenance request/grant | Family doctrine 2 (quoted below); `scoria_cmd_arbiter.sv` maintenance ports | `scoria_cmd_arbiter.sby` | PROVEN |
| Refresh interval/credit | `scoria_refresh_ctrl.sv` — `POSTPONE_MAX = MAX_PENDING - 2` derivation | `scoria_refresh_ctrl.sby` | PROVEN |
| ZQ calibration window | `scoria_cmd_arbiter.sv` — `w_out_safe` ZQ quiet term | `scoria_cmd_arbiter.sby` | PROVEN |
| Bank-timer spacing gates | `scoria_bank_timer.sv` — `safe_act_o/safe_rd_o/safe_wr_o/safe_pre_o` | `scoria_bank_timer.sby` | PROVEN |
| Global-timers next-state alignment | `scoria_global_timers.sv` — next-state derivation | `scoria_global_timers.sby` | PROVEN |
| Read-CAM issue contract | `scoria_rd_cmd_cam.sv` — issue-of-invalid-slot assertion | `scoria_rd_cmd_cam.sby` | ASSERTED |
| Return-ring input contracts | `scoria_rd_return_ring.sv` — return-without-ticket / issue-while-empty assertions | `scoria_rd_return_ring.sby` | ASSERTED |
| Write-CAM fill/commit/snarf | `scoria_wr_data_cam.sv` — fill/commit/drain queues | `scoria_wr_data_cam.sby` | PROVEN |
| CDC staged-token invariant | `scoria_dfi_cdc.sv` — write-burst-staged token FIFO | `scoria_dfi_cdc.sby` | PROVEN |
| Command-path no-pacing | `scoria_dfi_cmd_path.sv` — structural-holds-only comment | none | MEASURED |
| Arbiter final-gate drop-not-hold | `scoria_cmd_arbiter.sv` — `w_out_safe` rank-global terms | `scoria_cmd_arbiter.sby` (BUG001=0) | PROVEN |
| Init MR ordering | `scoria_init_sequencer.sv` — DDR3/LPDDR3 state-list fences | none | RTL fence |
| Write-leveling four-state telemetry | `scoria_wrlvl_ifc.sv` — state encoding and status outputs | none | RTL fence |

: Table 4.1: Anchor map — RTL anchors and formal verdicts

The line numbers are not pinned here; the generator's citation gate will pin them when it runs. Until then the named fence or assertion is the anchor.

## Contract: address decode

**Terms.** `axi_addr_i`, `bank_lsb_i`, `hash_en_i`, `hash_seed_i`, `rank_o`, `bank_o`, `row_o`, `col_o`.

**Invariants.**

1. The decode is injective inside the mappable range: two distinct word addresses never decode to the same `{rank,bank,row,col}` tuple (`a_injective` in `scoria_addr_mapper.sby`).
2. Equal word addresses decode identically (`a_deterministic`).
3. `row_o` and `rank_o` are invariant across legal `bank_lsb` values; only the bank/column split moves (`a_row_invariant`, `a_rank_invariant`).
4. An out-of-range `bank_lsb` clamps to `COL_WIDTH` (ROW_MAJOR) rather than producing an illegal slice (`a_clamp_*`).

**Decision table.** Rows where two different addresses alias, or where row/rank move with `bank_lsb`, or where an out-of-range `bank_lsb` produces a non-ROW_MAJOR decode, are `ILLEGAL`.

## Contract: DDR3 command decode and LPDDR3 CA encoding

**Terms.** `dfi_cs_n_o`, `dfi_ras_n_o`, `dfi_cas_n_o`, `dfi_we_n_o`, `dfi_bank_o`, `dfi_address_o`; `memtype_i` selects the encoding family.

**Invariants.**

1. For DDR3, the anchored truth table in `scoria_dfi_cmd_formatter.sv` enumerates exactly `NOP/ACT/RD/RDA/WR/WRA/PRE/PREA/REF/MRS/ZQCS/ZQCL`; every command the formatter issues is one of these rows.
2. Auto-precharge variants (`RDA`, `WRA`, `PREA`) are distinguished by the `AP` bit carried on `dfi_address_o[10]`, not by a separate pin.
3. For LPDDR3, the CA-bus word is bit-exact JESD209-2F Table 60, packed as `{w_ca_f, w_ca_r}` into `dfi_address_o`; `dfi_ras_n_o/cas_n_o/we_n_o` are held idle.
4. `dfi_odt_o` is driven from the mode-register ODT settings and transaction direction; it is not a static value.

**Decision table.** One row per (op, memtype) pair; rows that decode to a command outside the anchored set are `ILLEGAL`. The minimized qualifier SOPs for this table will be the kmap book's command table when the generator lands.

## Contract: maintenance request/grant

**Terms.** `refresh_req_o`/`refresh_grant_o` from `scoria_refresh_ctrl`, `zq_req_i`/`zq_grant_o` from `scoria_zq_ctrl`, and the arbiter's maintenance gating.

**Invariants.**

1. Family doctrine 2 applies in full: "Refresh, ZQ calibration, and their relatives are guests on the command bus. They raise a request, the scheduler grants them a window, and they wait their turn — they never preempt an in-flight host transaction."
2. `gnt` is exclusive: at most one maintenance source holds the bus in any cycle.
3. A refresh or ZQ calibration occupies the banks it touches for the operation's duration; the bank timers and the arbiter's `w_out_safe` quiet window own those banks.

**Decision table.** One row per (source, state) pair; rows where two sources hold `gnt`, or a source issues without `gnt`, or any command fires inside the ZQCS window, are `ILLEGAL`.

## Contract: refresh interval/credit

**Terms.** `t_refi_i`, `postpone_limit_i`, `pullin_limit_i`, `pending_refreshes_o`, `obs_pullin_credit_o`, `refresh_req_o`.

**Invariants.**

1. JEDEC permits at most 8 postponed refreshes; the backlog saturates at that ceiling (`a_pending_ceiling` in `scoria_refresh_ctrl.sby`).
2. `POSTPONE_MAX = MAX_PENDING - 2 = 6` gives two refreshes of headroom: the request asserts at a backlog of 7 before the accumulator saturates at 8 (`a_headroom`).
3. Pull-in credit stays inside the JEDEC +-8 window (`a_pullin_ceiling`).
4. The REFpb bank rotor advances by exactly one per accepted REFpb and only then, mirroring the device's internal counter (`a_rotor_advances_on_refpb`, `a_rotor_holds_without_refpb`).

**Decision table.** Rows where `pending_refreshes_o > 8`, or where the rotor steps without a REFpb grant, or where a backlog past `POSTPONE_MAX` does not raise `refresh_req_o`, are `ILLEGAL`.

## Contract: ZQ calibration window

**Terms.** `zq_req_i`, `zq_grant_o`, `t_zqcs_i`, `stall_zq_o`, the arbiter's `w_out_safe` final gate.

**Invariants.**

1. JESD79-3F 3.10 forbids every command during the `tZQCS` window.
2. The arbiter owns this obligation alone; `scoria_zq_ctrl` does not hold the window.
3. `scoria_cmd_arbiter.sby` proves `a_zqcs_quiet`: no ACT/RD/WR/PRE fires while `age_zq <= t_zqcs`.

**Decision table.** Any row with a command issued inside the ZQCS window is `ILLEGAL`.

## Contract: bank-timer spacing gates

**Terms.** `safe_act_o`, `safe_rd_o`, `safe_wr_o`, `safe_pre_o`, and the timing CSR inputs `t_rcd_i`, `t_rp_i`, `t_ras_i`, `t_rc_i`, `t_wr_i`, `t_rtp_i`.

**Invariants.**

1. The gate cannot open early: `a_trc`, `a_trp`, `a_trcd`, `a_tras`, `a_trtp`, `a_twr` in `scoria_bank_timer.sby` enforce the JEDEC windows.
2. The enforced bound is `N+1`, not `N`: the counter is loaded with the programmed value and opens the cycle after it would reach zero (`a_trc_bound_n1`, `a_trcd_bound_n1`, `a_tras_bound_n1`).
3. Structural implications used by the arbiter: `safe_act => !row_valid`; `safe_rd || safe_wr => row_valid`; `safe_pre => row_valid`; `ap_pending => row_valid`.
4. `safe_rd == safe_wr` in this RTL; a consumer that treats them differently is wrong.

**Decision table.** Rows where a command fires while the matching `safe_*` is low, or where the spacing is less than `N+1`, are `ILLEGAL`.

## Contract: global-timers next-state alignment

**Terms.** `tfaw_window_ok_o`, `trrd_window_ok_o`, `twtr_global_ok_o`, `trtw_window_ok_o`, `tccd_window_ok_o`, and their `obs_*` shadows.

**Invariants.**

1. The block derives its next state once and feeds both the counter flops and the readiness flops from it; there is no second derivation to fall out of step (the FIXED-FORM property that closed pumice ISSUE-018).
2. The environment contract is exactly the published flags plus one cycle of the consumer's own compensation; no extra hidden term is required.
3. `scoria_global_timers.sby` proves `a_trrd`, `a_tfaw`, `a_tccd`, `a_twtr`, `a_trtw`, and the `N+1` bound variants.
4. The debug view matches the scheduler view cycle-for-cycle (`a_obs_faw`, `a_obs_trrd`, `a_obs_twtr`, `a_obs_trtw`, `a_obs_tccd`).

**Decision table.** Rows where the consumer obeys the flags and a JEDEC window is still violated are `ILLEGAL`.

## Contract: read-CAM issue contract

**Terms.** `issue_valid_i`, `issue_slot_i`, `sch_valid_o`, `r_valid[issue_slot_i]`.

**Invariants.**

1. This is an input contract, not a property of the block: it constrains whoever issues, not the CAM.
2. `scoria_rd_cmd_cam.sv` carries a simulation-only assertion at the issue-of-invalid-slot check (`w_issue_fire && !r_valid[issue_slot_i]`).
3. `scoria_rd_cmd_cam.sby` takes the same statement as an assumption (`assume (!issue_valid_i || sch_valid_o[issue_slot_i])`) and proves ticket integrity and slot lifecycle under it.

**Decision table.** A row where `issue_valid_i` is high and the targeted slot is not valid is `ILLEGAL`.

## Contract: return-ring input contracts

**Terms.** `dfi_ret_valid_i`, `w_iq_rd_valid`, `issue_valid_i`, `w_empty`.

**Invariants.**

1. `assert (!(dfi_ret_valid_i && !w_iq_rd_valid))` — a return beat never arrives without a ticket in flight.
2. `assert (!(issue_valid_i && w_empty))` — a ticket is never issued while the ring is empty.
3. Both are environment contracts on the driver; `scoria_rd_return_ring.sby` restates them as assumptions and proves accounting, no-fabrication, and data integrity under them.

**Decision table.** Rows violating either invariant are `ILLEGAL`.

## Contract: write-CAM fill/commit/snarf ordering

**Terms.** `ins_valid_i/ready_o`, `wd_valid_i/ready_o`, `commit_valid_i/ready_o`, `cm_rd_valid_o/ready_i`, `snarf_probe_valid_i`, `snarf_hit_o`, `snarf_accept_i`.

**Invariants.**

1. A slot is not schedulable until it is fully filled; the scheduler view excludes not-yet-filled entries.
2. Commit is rate-matched: at most `WR_DRAIN_AHEAD` bursts sit in the drain queue, so a WR command cannot fire far ahead of its data.
3. Snarf returns the youngest matching filled entry; the snarf and commit streams share one BRAM read port with commit priority and a starvation limit.
4. `scoria_wr_data_cam.sby` proves burst framing (`a_burst_len`) and slot lifecycle (`a_ins_ready_implies_free`).

**Decision table.** Rows where a commit fires before fill completion, where snarf returns a stale entry, or where burst framing is violated are `ILLEGAL`.

## Contract: CDC staged-token invariant

**Terms.** `wd_valid_i`, `wd_last_i`, `wd_ready_o`, `pwr_staged_valid_o`, `pwr_staged_pop_i`.

**Invariants.**

1. A write burst crosses as data words plus, on the last word, a one-bit "burst staged" token in a second FIFO.
2. The command path pops one token per WR it accepts, so a WR command can never reach the PHY ahead of its data.
3. `scoria_dfi_cdc.sby` proves `a_no_extra_staged`: the PHY never pops more staged bursts than the controller completed.

**Decision table.** Rows where a token crosses without its data, or data crosses without its token, are `ILLEGAL`.

## Contract: command-path no-pacing

**Terms.** `cmd_valid_i`, `cmd_ready_o`, `wr_op_ready_i`, `rd_op_ready_i`.

**Invariants.**

1. `scoria_dfi_cmd_path.sv` does not pace commands; all timing lives in the scheduler.
2. The only remaining holds are structural: a read may not issue unless the read aligner has a free slot, and a write may not issue unless its data has crossed and is staged.
3. TASK-007 measured the structural-hold profile; intentional pacing in the command path was removed because it compressed JEDEC spacing behind the hold.

**Verdict.** MEASURED, not formally proven as a contract. The property is that no timing-dependent hold exists in this path.

## Contract: arbiter final-gate drop-not-hold

**Terms.** `w_out_safe`, `bank_act_ready_i`, `tfaw_ok_i`, `trrd_ok_i`, `bank_rdwr_ready_i`, `twtr_ok_i`, `trtw_ok_i`, `tccd_ok_i`.

**Invariants.**

1. The final gate re-validates both per-bank readiness and rank-global windows (`tfaw_ok`, `trrd_ok`) at the cycle the command fires.
2. BUG-001 was the failure mode: an earlier sampling of the rank-global terms let two cross-bank ACTs violate `tRRD`. The fix adds the rank-global terms to `w_out_safe`.
3. `scoria_cmd_arbiter.sby` proves `a_trrd_spacing` and `a_tfaw_window` with `BUG001 = 1`; the `nofix` task runs with `BUG001 = 0` to show the failure mode.
4. BUG-003 is the same shape for ZQ: the final gate drops the command rather than holding it, preserving spacing.

**Decision table.** Rows where a command fires while any relevant `*_ok` or per-bank ready is low are `ILLEGAL`.

## Contract: init MR ordering

**Terms.** `init_cmd_valid`, `init_cmd_op`, `init_cmd_bank`, `init_cmd_row`, the init FSM state list.

**Invariants.**

1. DDR3 order is fixed by the state list: `S_D3_RSTN` → `S_D3_CKE` → `S_D3_XPR` → `S_D3_MR2` → `S_D3_MR3` → `S_D3_MR1` → `S_D3_MR0` → `S_D3_ZQCL` → `S_D3_LOCK` → `S_DONE`.
2. LPDDR3 order is `S_L_RESET` → `S_L_ZQ` → `S_L_MR1` → `S_L_MR2` → `S_L_MR3` → `S_DONE`.
3. MR0 load ORs in `DDR3_DLL_RESET = 16'h0100`; the shadow is written with the unmodified `mr0_i`.

**Decision table.** Rows where the MR order is violated, or where `RESET#` is re-asserted without `init_force_restart`, are `ILLEGAL`.

## Contract: write-leveling four-state telemetry

**Terms.** `wrlvl_result`, `wrlvl_result_valid`, `wrlvl_timeout`, `wrlvl_ever_done`, `wrlvl_state`, `strobe_i`, `prime_dq_i`.

**Invariants.**

1. The four observable outcomes are {never attempted, converged, timed out, swept with no flip}; each has a distinct encoding in the status registers.
2. "Never attempted" is the reset state (`WL_OFF`); a detector that has never fired must be representable.
3. Timeout is distinguishable from no-result: `t_wlmrd_max` is a controller-defined timeout with its own status bit (`wrlvl_timeout`).
4. The state machine has no delay-walk states; firmware performs the search. `tWLOE` is inert because only the prime DQ bit is sampled.

**Decision table.** Rows where timeout and no-result share an encoding, or where a search state appears in the state list, are `ILLEGAL`.

## Regenerating the workbook

There is no scoria kmap generator run yet. This chapter is the citation-ready anchor map for when one lands. Do not hand-edit a future `scoria_signal_contracts.xlsx`; it must be a build artifact of the generator, and the citation gate must fail the run if any RTL anchor drifts from the anchors named above.
