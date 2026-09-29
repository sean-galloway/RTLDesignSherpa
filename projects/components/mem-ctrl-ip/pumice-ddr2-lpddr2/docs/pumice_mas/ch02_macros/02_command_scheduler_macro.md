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

# `pumice_mem_cmd_scheduler` (command scheduler macro)

**Module:** `pumice_mem_cmd_scheduler.sv`
**Location:** `rtl/macro/`
**Category:** Layer-2 macro (the decision layer of `pumice_core`)
**FUBs bundled:** arbiter + bank/global timers + refresh + init + mode reg + cmd FIFO

## Purpose

"What command should we issue this cycle?" -- the decision-making layer. It
wires the command arbiter to the per-bank safe timers, the global (bus/rank)
turnaround timers, the refresh controller, the init sequencer plus mode-register
shadow, and an output command FIFO. It emits a single abstract DRAM command
stream `{op, rank, bank, row, col, ap}` for the DFI layer to phase-pack.

The scheduler is **single-issue**, **PHY / nphases-agnostic**, and runs on a
single controller clock (`aclk`). The CAM sched-lookup / oldest / commit / issue
ports are **external** -- the CAMs live in `pumice_axi4_ifc`. This replaces the
old `command_scheduler_macro` (`scheduler` / `xbank_timers` / `page_predictor` /
`powerdown_ctrl` etc.); those names are retired.

## FUBs

| FUB                   | Role                                                                                                    |
|-----------------------|---------------------------------------------------------------------------------------------------------|
| `pumice_cmd_arbiter`  | The single pick core. Picks one command per cycle from the CAM lookups + oldest snapshots under page policy; open-page decision is **inline** here (no separate predictor). Drives the write `commit` / read `issue` handshakes and the per-command `evt_*` strobes; emits the abstract command. |
| `pumice_bank_timers`  | Stamps a `bank_timer` per (rank,bank) and fans the `evt_*` strobes; produces `bank_act/rdwr/pre_ready`, `bank_row_active`, `bank_open_row`. |
| `bank_timer`          | FSM-free per-bank JEDEC safe timers (tRCD/tRP/tRAS/tRC/tWR/tRTP) + a row-open register + a single auto-precharge bit. Combinational readiness off the countdown timers. |
| `global_timers`       | Cross-bank/rank turnaround windows: tFAW + tRRD per rank, tWTR/tRTW/tCCD global. Produces `_ok` window flags. |
| `refresh_ctrl`        | tREFI down-counter + 8-deep postpone; `refresh_req`/`refresh_drain` to the arbiter, `refresh_grant` back. Enabled after init. |
| `init_sequencer`      | DDR2 + LPDDR2 JEDEC MRS init microprogram. Drives `dfi_init_start_o`, emits init commands into the arbiter, and writes the MR shadow. Gates traffic until `init_done`. |
| `mode_register`       | MR shadow updated by the init MRS writes; decodes CL / CWL / BL (and AL / drive-strength / ODT). Supplies `cl_o`/`cwl_o`/`bl_o` to the DFI layer. |
| `gaxi_fifo_sync`      | Output command FIFO (`CMD_FIFO_DEPTH`), packs `{ap, col, row, bank, rank, op}` (`CMD_W` bits) into the abstract command stream to the DFI layer. |

## FSM-Free Bank Timing

`bank_timer` is deliberately **stateless-in-the-control-sense**: preset /
decrement countdown timers (rcd/ras/rc/rp/preblk), a row-open register, and one
auto-precharge bit -- no multi-state bank machine. The per-command
`safe_act/rd/wr/pre` outputs are combinational off the timers with a single
register stage, so the arbiter reads readiness with one cycle of latency. This
replaced the old double-registered 3-state bank FSM (retired `bank_machine`),
which caused refresh-vs-ACT and column-vs-PRE hazards. `pumice_bank_timers`
stamps the timer per (rank,bank).

## External Boundaries

- **CAM sched ports (to `pumice_axi4_ifc`):** for each of write and read, the
  `N_LU = NUM_BANKS` lookup buses (`lu_valid/bank/row` out; `hit/slot/col/id/age`
  in), the `oldest_*` snapshot in, and the write `commit_*` / read `issue_*`
  handshake out.
- **Command stream out (to `pumice_dfi_layer`):**
  `cmd_valid/ready` + `{op, rank, bank, row, col, ap}`.
- **Mode-register shadow out:** `cl_o` / `cwl_o` / `bl_o` to the DFI layer.
- **Init handshake:** `dfi_init_start_o` out and `dfi_init_complete_i` in
  (routed to/from the PHY via the DFI layer); `init_done_o` status out.
- **Config in:** the JEDEC timings (tRCD/tRP/tRAS/tRC/tWR/tRTP/tFAW/tRRD/tWTR/
  tRTW/tCCD/tREFI), `refresh_burst`, the init waits
  (`t_init_wait`/`t_dll_wait`/`t_mrd_wait`/`t_rp_wait`/`t_rfc_wait`),
  `page_policy_i`, and `memtype_i` -- all delivered from the CSR by name.

`busy_o` asserts while not init-done, on a pending refresh, while a command is
buffered in the FIFO, or while any bank row is active.

## Tests

The scheduler has a macro-level test that exercises the arbiter against the two
real CAMs -- combinational pickers must be macro-tested, since registered
feedback latency can hide double-issue hazards that a FUB-only test misses. Each
constituent FUB also has its own unit test in `dv/tests/fub/`.
