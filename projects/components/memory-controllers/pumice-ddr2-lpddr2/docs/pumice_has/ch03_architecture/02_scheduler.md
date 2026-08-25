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

# Command Scheduler

The command-scheduling layer is `pumice_mem_cmd_scheduler` (`rtl/macro/pumice_mem_cmd_scheduler.sv`). It is a single controller-clock (`aclk`) layer that wires together the pick core and all the timing / bring-up support blocks, and emits one abstract DRAM command stream `{op, rank, bank, row, col, ap}` into a command FIFO for the DFI layer to pack onto phases.

The scheduler does **not** hold the transaction queue — pending requests live in the two CAMs inside `pumice_axi4_ifc`. The scheduler reads them through external lookup / oldest / commit / issue ports.

## Composition

`pumice_mem_cmd_scheduler` instantiates:

- **`pumice_cmd_arbiter`** — the single pick core (open-page decision is inline).
- **`pumice_bank_timers`** (per-rank/bank `bank_timer` instances) — FSM-free per-bank JEDEC "safe" timers (see `03_bank_machines.md`).
- **`global_timers`** — cross-bank / bus turnaround (tFAW, tRRD, tWTR, tRTW, tCCD).
- **`refresh_ctrl`** — tREFI tracking + postpone accumulator (see `04_refresh.md`).
- **`init_sequencer`** — JEDEC MRS cold-boot init; gates traffic until done (see `05_init_power.md`).
- **`mode_register`** — CL / CWL / BL decode shadow, updated by init MRS writes.
- an output command FIFO (`gaxi_fifo_sync`).

## `pumice_cmd_arbiter`

### Purpose

Pick exactly one abstract DRAM command per cycle and push it into the scheduler-to-DFI command interface. It is PHY/nphases-agnostic and single-issue. JEDEC timing readiness is supplied by the per-bank (`pumice_bank_timers`) and global (`global_timers`) inputs; the arbiter never re-derives timing itself.

### Inputs

- Per-bank readiness from `pumice_bank_timers`: `bank_act_ready`, `bank_rdwr_ready`, `bank_pre_ready`, `bank_row_active`, `bank_open_row`.
- Global readiness from `global_timers`: `tfaw_ok`, `trrd_ok` (per-rank), `twtr_ok`, `trtw_ok`, `tccd_ok`.
- Per-bank scheduler lookups into both CAMs (query each bank's open row), plus the CAMs' `oldest` ports.
- Refresh request / drain from `refresh_ctrl`; init command passthrough from `init_sequencer`.

### Outputs

- Command push `{op, rank, bank, row, col, ap}` with `cmd_valid` / `cmd_ready`.
- Event strobes to the timers (`evt_act`, `evt_rd`, `evt_wr`, `evt_pre`, `evt_ap`, `evt_rank`, `evt_bank`, `evt_row`) — fired only on an accepted issue.
- CAM side effects: write-CAM commit, read-CAM issue, refresh grant — all gated on accepted issue.

`op` is drawn from `dram_op_e` (`OP_NOP`, `OP_ACT`, `OP_RD`, `OP_RDA`, `OP_WR`, `OP_WRA`, `OP_PRE`, `OP_PREA`, `OP_REF`, `OP_REFPB`, `OP_MRS`, ...).

### Priority Function

Evaluated combinationally each cycle (descending priority):

1. **Init in progress** (`!init_done`) — forward the `init_sequencer` command verbatim; block all normal traffic.
2. **Refresh** (`refresh_req` or drain active) — precharge active banks one per cycle, then — only under `w_ref_safe` (all rows closed in the registered view, nothing row-affecting in flight or guarded, prior REF's tRFC recovery elapsed) — issue `REF` and assert the refresh grant. Each fired REF loads the arbiter's tRFC down-counter (`TIMINGS_RFC_REFI.tRFC`); while non-zero, ACTs and further REFs are blocked.
3. **Column row-hit** — a `RD`/`WR` to an already-open row whose bank is column-ready (`bank_rdwr_ready`) and whose bus turnaround permits it (`tccd_ok` + `twtr_ok` for reads / `trtw_ok` for writes). **Reads have priority over writes**; within each, the **oldest** entry (max CAM relative age) wins the tie-break.
4. **Fallback** — no ready row-hit: `ACT` the oldest pending op's row on an idle bank (subject to `tfaw_ok` / `trrd_ok` and the ACT/PRE guard), or `PRE` a bank that is open on the wrong row.

The fallback target is read-priority: the read CAM's `oldest` port is consulted first, then the write CAM's.

### ACT/PRE Re-Issue Guard

The bank timers register their readiness outputs (there is a two-cycle latency from an event to `act_ready` / `pre_ready` dropping). A stateless combinational arbiter would otherwise re-issue ACT/PRE to the same bank before the timers reflect it. The arbiter therefore keeps a two-cycle per-bank guard (`r_guard0` / `r_guard1`) that blocks a bank for two cycles after an accepted ACT, PRE **or column** to it — columns are included because a just-fired column has not yet dropped the bank's registered `pre_ready` (tRTP/tWR load), so an unguarded PRE (normal or refresh-drain) could precharge on stale readiness. Columns still self-limit against each other (both CAMs exclude a just-committed / just-issued slot from the next cycle's lookup), so the guard never gates column-vs-column. The shared-DQ-bus burst-occupancy constraint (a BL burst owns the bus for `BL/DFI_RATE` DFI cycles) is enforced downstream in the DFI command path, not here; the CDC decouples `aclk` command issue from the `dfi_clk` DQ timing.

### Page Policy (Auto-Precharge)

The column auto-precharge bit is set directly from `page_policy_i`:

- **`OPEN`** — `ap = 0`; rows stay open. Column ops stream to an open row at tCCD rate.
- **`CLOSE`** — `ap = 1`; every column op auto-precharges (issues `RDA` / `WRA`).
- **Adaptive policies** — the runtime page-policy engine (`pumice_page_policy`, `PAGE_POLICY_CFG.policy_mode`): `fixed_open` idle-timeout close and Ghasempour-2015 `adapt_time`. (The former `HAPPY_HYBRID` enum encoding and `page_predictor.sv` are retired; the encoding maps to build default.)

The open-page "keep the row open" decision therefore lives inline in the arbiter and the per-bank `bank_timer` (which keeps the row open on `RD`/`WR`), not in a separate predictor or lookahead unit.

### Issue Rate

One command issue per controller clock cycle. Multi-phase / multi-cycle placement (including LPDDR2's 2-edge CA word) happens downstream in the DFI layer, so the arbiter always sees a single issue.

## Mode Register Shadow

`mode_register` maintains the live CL / CWL / BL decode. Its shadow is written in lockstep by the `init_sequencer` MRS writes (`mr_seq_we` / `mr_seq_index` / `mr_seq_data`), so the controller's timing decode tracks exactly what was programmed into the DRAM during init. It exposes `cl_o` / `cwl_o` / `bl_o` to the DFI layer.

## v1 Scope Notes

The arbiter picks from a single rank (rank 0) in v1; write-drain watermarking, multi-rank pick, and power-down coordination are documented TODOs. The `busy_o` output aggregates "init not done", "refresh pending", "command in the FIFO", and "any bank row active".
