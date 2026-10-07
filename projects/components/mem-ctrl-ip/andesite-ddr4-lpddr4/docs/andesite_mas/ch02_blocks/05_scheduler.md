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

# Scheduler and Command Arbiter (`andesite_scheduler_layer` + `andesite_cmd_arbiter`)

**Module:** `andesite_scheduler_layer.sv`, `andesite_cmd_arbiter.sv`
**Location:** `rtl/macro/` (scheduler), `rtl/fub/` (arbiter)
**Category:** scheduling / arbitration
**Parent:** `andesite_core`
**Status:** carried from scoria and landed — arbiter carries the L/S delta; the tables below name the landed port lists. The macro's init/mode-register instances are rewired to the P1 blocks (macro-integration pass, 2026-10-05): the P1 `init_sequencer` is self-timed and DDR4-only, and the P1 `mode_register` policy outputs are the macro's observability contract.

---

## Purpose

The scheduler picks which ready command goes to the formatter each cycle. It inherits scoria's FR-FCFS arbiter and its maintenance request/grant channel. The andesite delta is L/S-aware issue: DDR4 bank groups add a same-group versus cross-group split to the command-spacing checks, and the global timers grow the `tCCD_L/S` and `tRRD_L/S` pairs. LPDDR4 has no bank groups, so the long and short checks collapse to one.

The scheduler never invents a new arbitration philosophy. It takes scoria's mechanism and teaches it about bank groups.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `NUM_RANKS` | int | 1+ | 1 | ranks per channel |
| `NUM_BANKS` | int | 8..16 | 8 | banks per rank |
| `NUM_BG` | int | 1..4 | 4 | bank groups; `1` is the LPDDR4 degeneration (the L/S delta parameter) |
| `NUM_ENTRIES` | int | 8..32 | 8 | read and write CAM depth |
| `AGE_WIDTH` | int | — | 16 | age-counter width |

: Table 2.5.1: Scheduler parameters

`NUM_BG = 1` is how LPDDR4 degenerates gracefully. There is no `if (memtype == LPDDR4)` branch in the issue check; the group index is constant and the L/S counters collapse by construction.

## Interface

### Host-side command ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `aclk` | in | 1 | controller clock |
| `aresetn` | in | 1 | active-low reset |
| `init_done_i` | in | 1 | scheduler admits no host commands until high |
| `rd_sch_valid_i` | in | `NUM_ENTRIES` | read CAM per-entry valid (the CAMs live in the intake/AXI interface) |
| `wr_sch_valid_i` | in | `NUM_ENTRIES` | write CAM per-entry valid |
| `rd_sch_bank_i` | in | `NUM_ENTRIES*BKW` | read candidate bank per entry; `rd_sch_row_i`/`rd_sch_col_i` carry the rest of the payload |
| `wr_sch_bank_i` | in | `NUM_ENTRIES*BKW` | write candidate bank per entry; `wr_sch_row_i`/`wr_sch_col_i` alongside |
| `rd_sch_older_i` | in | `NUM_ENTRIES^2` | read CAM age-order matrix; the write side is `wr_sch_older_i` |
| `rd_issue_valid_o` | out | 1 | read command wins this cycle; `rd_issue_slot_o` names the winning entry |
| `wr_commit_valid_o` | out | 1 | write command wins this cycle; `wr_commit_slot_o` names the winning entry |
| `cmd_valid_o` | out | 1 | issued command strobe toward the formatter path; `cmd_op_o`, `cmd_rank_o`, `cmd_bank_o`, `cmd_row_o`, `cmd_col_o`, `cmd_ap_o` carry it, `cmd_ready_i` back-pressures |
| `cmd_bg_o` | out | `$clog2(NUM_BG)` | bank group of the issued command (the arbiter's registered-pick group, `bank[BKW-1 -: BGW]`); rides the widened command word `{ap,col,row,bg,bank,rank,op}` to the DFI formatter |

### Bank-group timing ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `tccd_ok_i` | in | 1 | `tCCD` base spacing ok (cross-group; the LPDDR4 degenerate check) |
| `tccd_l_ok_i` | in | 1 | `tCCD_L` same-group spacing ok — the andesite L/S delta input |
| `trrd_ok_i` | in | 1 | `tRRD_S`-class ACT-to-ACT ok, per rank |
| `trrd_l_ok_i` | in | 1 | `tRRD_L` same-group ACT-to-ACT ok — L/S delta input |
| `tfaw_ok_i` | in | 1 | `tFAW` four-activate window ok, per rank |
| `twtr_ok_i` | in | 1 | write-to-read turnaround ok; `trtw_ok_i` is the read-to-write partner |
| `bank_act_ready_i` | in | `NUM_RANKS x NUM_BANKS` | per-bank timer readiness (activate); `bank_rdwr_ready_i`, `bank_pre_ready_i` and the `_la_i` lookahead variants ride alongside |

The L/S counters live in the global timers; the arbiter consumes the ok flags. The bank group of the last-issued command is tracked inside the arbiter (`r_last_col_bg`, `r_last_act_bg`), not on a port — there is no `last_cmd_group` signal.

### Maintenance request/grant ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `refresh_req_i` | in | 1 | refresh wants the bus (from `refresh_ctrl`) |
| `refresh_grant_o` | out | 1 | bus granted to refresh |
| `refresh_drain_i` | in | 1 | refresh drain in progress; CAMs hold |
| `refresh_kind_i` | in | 1 | 0 = all-bank `REF`, 1 = per-bank (LPDDR4) |
| `refresh_bank_i` | in | `BKW` | per-bank target mirror (the rotor) |
| `zq_req_i` | in | 1 | ZQ calibration wants the bus (from `zq_ctrl`) |
| `zq_grant_o` | out | 1 | bus granted to ZQ |

The carried RTL keeps scoria's two request/grant pairs — one for refresh, one for ZQ — rather than one unified `maint_req`/`maint_tag` channel; the unified tagged channel stays the conceptual model, and the formatter-facing tag is derived downstream. The ODT turnaround request lands with `odt_ctrl` (Ch 2.8). The rule is inherited from scoria: request and wait, never preempt.

: Table 2.5.2: Scheduler interface

## Macro init/policy interface (P1 rewiring, landed 2026-10-05)

The scheduler macro owns the P1 `init_sequencer` and `mode_register`
instances. The scoria DDR3-era connections (`mc_clk`-style pins, the
`dfi_init_start`/`dfi_init_complete` PHY handshake, and the CL/CWL/BL shadow
outputs) retired with the rewiring — the P1 sequencer is self-timed
(`tINIT*` CSRs; any non-DDR4 `memtype` latches `init_err`) and the P1
register never carried latency shadows.

| Signal | Direction | Width | Description |
|---|---|---|---|
| `t_init_wait_i` | in | 16 | `tINIT1` — RESET# low time |
| `t_rp_wait_i` | in | 8 | `tINIT3` — RESET# release to CKE (zero-extended) |
| `t_cke_wait_i` | in | 16 | `tINIT4` — CKE to first MRS |
| `t_mrd_wait_i` | in | 8 | `tMRD` — MRS-to-MRS gap (zero-extended) |
| `t_mod_wait_i` | in | 16 | `tMOD` — last MRS to ZQCL |
| `t_dll_wait_i` / `t_zqinit_wait_i` | in | 16 | `tDLLK` / `tZQinit` |
| `mr0_i` … `mr6_i` | in | 16 ×7 | DDR4 MR images; the P1 FSM writes MR3, MR6, MR5, MR4, MR2, MR1, MR0 |
| `dram_reset_n_o` / `cke_o` | out | 1 | DRAM RESET# / CKE pins, driven by the P1 init FSM |
| `init_done_o` / `init_err_o` | out | 1 | init complete / unsupported-memtype or watchdog error |
| `zq_cal_start_o` | out | 1 | status strobe marking the init FSM's ZQCL issue (the ZQCL itself rides the command stream) |
| `gear_down_entry_o` / `ca_train_start_o` / `parity_enable_o` | out | 1 | P1 init-FSM status outputs (parity latches on at MR5 per the init sequence) |
| `rtt_nom_o` / `rtt_wr_o` / `rtt_park_o` | out | 3 | ODT policy images (the `odt_ctrl` observability contract) |
| `rd_dbi_en_o` / `wr_dbi_en_o` | out | 1 | MR5 read/write DBI enables (the DFI datapath consumers) |
| `mpr_page_o` / `fgr_factor_o` / `ca_parity_lat_o` / `lpddr4_odt_o` | out | 2 / 2 / 2 / 3 | MR3 MPR page, FGR factor, CA-parity latency, LPDDR4 ODT image |
| `wrlvl_en_o` | out | 1 | MR1[7] — write-leveling mode authority (to the training layer) |

Init commands (MRS / ZQCL) reach the DRAM through the ordinary command
stream: the P1 `cmd_req`/`cmd_ack` handshake is honored by the arbiter's
accept pulse (`cmd_ack` = accept qualified by `OP_MRS`/`OP_ZQCL`), and the
arbiter forwards the init payload (`cmd_addr` low bits) on the stream's row
field, exactly as the carried scoria forwarding did. The init MR index
rides `cmd_bank` into the mode-register store's write address.

## Microarchitecture internals

### FR-FCFS admission with L/S awareness

scoria's FR-FCFS arbiter is unchanged in spirit. Each candidate command is scored by age and readiness, and the highest scorer that passes the timing checks is granted. The andesite change is inside the timing check.

```text
issue_ok(cmd) = bank_timers.ok(cmd)
                AND global_timers.ok(cmd, group(cmd), group(last_cmd))
```

`group(cmd)` is the bank group of the candidate's bank. For a read or write command, the global-timer check now depends on whether the candidate targets the same bank group as the last-issued command:

- Same group: `tCCD_L` and `tRRD_L` apply.
- Different group: `tCCD_S` and `tRRD_S` apply.

The check also covers the outstanding same-group spacing obligations a burst of commands to one group leaves behind; the last-issued group registers (`r_last_col_bg`, `r_last_act_bg`) and the L/S ok flags carry that state into the admission check.

### Global timers

The global timer block inherits scoria's counters and adds four new ones. All are runtime CSRs.

| Counter | JEDEC symbol | Applies |
|---|---|---|
| `tCCD_L` | `tCCD_L` | same bank group |
| `tCCD_S` | `tCCD_S` | different bank groups |
| `tRRD_L` | `tRRD_L` | same bank group, activate-to-activate |
| `tRRD_S` | `tRRD_S` | different bank groups, activate-to-activate |

These join the inherited `tCCD`, `tRAS`, `tRC`, `tRP`, `tRCD`, `tWTR`, `tRTW`, `tWR`, and the read/write turnaround set. The values are runtime CSRs, initialised from the JESD79-4/JESD209-4 speed bin at CSR-derivation time (HAS Ch 5; numeric constants are HAS open question Q1).

### Maintenance request/grant semantics

The carried RTL keeps scoria's channel shape: two request/grant pairs into the arbiter, one for refresh (`refresh_req_i`/`refresh_grant_o`) and one for ZQ (`zq_req_i`/`zq_grant_o`). The original spec sketch on this page was one unified `maint_req` with a `maint_tag` source identifier; the carry ruled that the inherited pairs are the truth this tier, and the tag survives only as the conceptual model the formatter-side maintenance encoding derives from.

| Source | Arbiter channel | Action when granted |
|---|---|---|
| `refresh_ctrl` | `refresh_req_i`/`refresh_grant_o` | issue `REF` or LPDDR4 per-bank refresh |
| `zq_ctrl` | `zq_req_i`/`zq_grant_o` | issue `ZQCS`, `ZQCL`, or LPDDR4 MPC ZQ calibration |
| `andesite_training_layer` | `trn_cmd_req_i`/`trn_cmd_grant_o` | issue training `MRS` or `MPC`; request-and-wait, all-banks-idle two-step shape like refresh |
| `odt_ctrl` | lands with Ch 2.8 | issue the ODT turnaround command or NOP-with-ODT |

The rule is inherited from scoria: request and wait, never preempt. A maintenance source raises its `req` and holds it until `grant` arrives. It cannot yank the bus away from an in-flight host command.

### LPDDR4 degeneration

LPDDR4 has no bank groups, so `NUM_BANK_GROUPS = 1` and `group(cmd)` is always zero. The same-group and cross-group checks collapse into a single check per pair because there is only one group to compare against. The L/S counters still exist, but they are loaded with the same value. This must fall out of the parameterization, not out of an `if (memtype == LPDDR4)` branch.

This is worth stating plainly: LPDDR4 is not a special case in the arbiter. It is the `NUM_BANK_GROUPS = 1` corner of the same code.

## FSM policy

The arbiter is priority logic plus CAMs, not an FSM. That is inherited from scoria. The scheduler's grant sequencing — one command per cycle, maintenance highest, FR-FCFS among host commands — is the same mechanism with the L/S inputs added.

The global timers are counters, not a state machine. Each timer decrements every cycle and asserts its `ok` flag at zero.

## Timing

One grant per cycle, as inherited. The new counters add combinational delay to the admission check but no new pipeline stages. The critical path is:

1. Read CAM and write CAM produce candidates.
2. Bank timers check per-bank readiness.
3. Global timers check L/S spacing; the last-issued group registers select the long or short window.
4. FR-FCFS priority selects the winner.
5. Grant is registered and the command is issued.

The counter values are runtime CSRs, initialised from the JESD79-4/JESD209-4 speed bin at CSR-derivation time (HAS Ch 5; numeric constants are HAS open question Q1).

## Notes

- **Why pairs, not a unified tagged channel:** the carried RTL is scoria's two request/grant pairs, kept byte-behavioral. The scheduler doesn't need to know what kind of maintenance it is granting; it only needs to know that maintenance beats host traffic and that only one source wins per cycle. A unified `maint_req`/`maint_tag` channel stays on the books as the conceptual model, not the landed interface.
- **L/S vs the old `tCCD`:** The inherited `tCCD` is kept as a fallback for modes where bank-group information is not available, but the primary check is the L/S pair. DV must prove that `tCCD_L` and `tCCD_S` subsume the old `tCCD` correctly for DDR4 and collapse to it for LPDDR4.
- **Maintenance starvation:** Because maintenance never preempts, a pathological stream of host commands could delay refresh or ZQ. The refresh controller's credit window and the ZQ controller's overdue counter handle this at the source; the scheduler's only obligation is fair arbitration once the request is raised.

## cmd_history_checker's DDR4 growth (landed 2026-10-04)

The checker's spacing-parameter set now carries the long/short pairs the
bank-group scheduler defines: `T_CCD_L`/`T_CCD_S` (CAS-to-CAS within /
across a bank group) and `T_RRD_L`/`T_RRD_S` (ACT-to-ACT), all runtime
parameters inert at 0, plus a `cmd_bg_i` bank-group command input. scoria's
nine checks are byte-identical; checks (10)-(13) are additive. The ported
suite proves each new check fires with its own fatal text (`fires_tccd_l/s`,
`fires_trrd_l/s`) and that legal streams at both minima stay silent
(`legal_ls_pairs_at_the_minimum`).
