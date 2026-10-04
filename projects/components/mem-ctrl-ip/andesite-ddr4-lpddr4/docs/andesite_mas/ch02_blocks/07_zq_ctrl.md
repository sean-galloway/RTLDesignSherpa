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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# ZQ Calibration Controller (`andesite_zq_ctrl`)

**Module:** `andesite_zq_ctrl.sv` (+ `zq_ctrl_mpc_lpddr4.sv` — lands with the MPC delta)
**Location:** `rtl/fub/`
**Category:** maintenance / calibration
**Parent:** `andesite_core`
**Status:** DDR4 core carried from scoria and landed; the LPDDR4 MPC submodule is specified below and lands with the ZQ task; ports table reconciled to the landed port list

---

## Purpose

`zq_ctrl` issues periodic ZQ calibration. For DDR4, the block is scoria's module carried unchanged: interval CSR, request-and-wait grant, `tZQCS` enforced by holding the next interval, issued-calibration counter, and CSR-selectable placement policy. For LPDDR4, calibration moves onto the MPC command, so a new submodule sequences it through the formatter's LPDDR4 CA path.

The DDR4 side is INHERITED. The LPDDR4 side is NEW. Both share one maintenance request port to the scheduler with a source tag.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| — | — | — | — | (no parameters; the interval and overdue widths are fixed on the ports — 32-bit interval, 13-bit overdue) |

: Table 2.7.1: ZQ controller parameters

## Interface

### Common ports (the landed DDR4 core)

| Signal | Direction | Width | Description |
|---|---|---|---|
| `mc_clk` | in | 1 | controller clock |
| `mc_rst_n` | in | 1 | active-low reset |
| `enable_i` | in | 1 | calibration engine enable (ZQ_CFG.zq_enable) |
| `t_zqcs_interval_i` | in | 32 | calibration interval, runtime CSR; 0 = off |
| `t_zqcs_i` | in | 16 | `tZQCS` recovery, runtime CSR |
| `placement_i` | in | 2 | placement policy select (Mode C) |
| `overdue_max_i` | in | 13 | defer-under-demand threshold |
| `demand_i` | in | 1 | demand indication from the scheduler side |
| `zq_req_o` | out | 1 | request to the scheduler; held until `zq_grant_i` — request-and-wait, never preempt |
| `zq_grant_i` | in | 1 | scheduler grant |
| `obs_busy_o` | out | 1 | a calibration is in flight |
| `obs_zqcs_total_o` | out | 16 | issued-calibration counter |
| `obs_interval_cnt_o` | out | 32 | interval countdown observability |
| `obs_overdue_o` | out | 1 | overdue flag (placement policy) |

The carried DDR4 core exposes no DDR4-only ports beyond this set: `ZQCS` is its only calibration flavour, and the init-time long calibration is sequenced by the scheduler macro's `t_zqinit_wait_i` window, not by this block. The original spec sketch's `init_zqcl_req`/`init_zqcl_done` handshake and the unified `maint_req`/`maint_tag` channel are not how the carried RTL works — the core requests calibration on `zq_req_o` and waits on `zq_grant_i`.

### LPDDR4-only ports (land with the MPC submodule)

No MPC ports exist yet. The submodule lands with the ZQ task per the FSM below; its ports (`mpc_zq_start`, `mpc_zq_latch`, `mpc_op`, `mpc_done` in the original sketch) will be reconciled to its landed list when it does, exactly as this table was.

: Table 2.7.2: ZQ controller ports

## Microarchitecture internals

### DDR4 path: inherited from scoria

The DDR4 core is scoria's `zq_ctrl`, unchanged. It implements:

- Interval CSR: countdown to the next calibration event.
- Request-and-wait grant: it asks the scheduler and waits; it never preempts.
- `tZQCS` enforcement: the next interval is held until the recovery time expires.
- Issued-calibration counter: tracks how many calibrations have gone out.
- CSR-selectable placement policy: scoria TASK-001 Mode C, baseline versus defer-under-demand with `overdue_max`.

For the internal details, see scoria's HAS Ch 3.2 and the landed RTL in `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/zq/`. This MAS page does not re-specify what already exists; it cites it.

### LPDDR4 path: new MPC submodule

LPDDR4 carries calibration on the MPC command, not dedicated `ZQCS`/`ZQCL` opcodes. The new submodule issues the ZQCal start and ZQCal latch opcodes through the formatter's LPDDR4 CA submodule.

```text
MPC_IDLE
    -> MPC_ISSUE   (assert cmd_req, wait for scheduler grant, drive MPC ZQCal start)
    -> MPC_WAIT    (wait tZQ latched from CSR)
    -> MPC_DONE    (drive calibration complete, reload interval counter)
    -> MPC_IDLE
```

`tZQ` here is the LPDDR4 ZQ calibration latency, a runtime CSR loaded from JESD209-4 at CSR-derivation time. The submodule will share the core's `obs_zqcs_total_o`/`obs_overdue_o` telemetry so one counter set serves both memtypes.

The MPC submodule depends on the LPDDR4 CA path in `dfi_cmd_formatter` (Ch 2.1). It does not build its own CA encoder; it drives the MPC opcode and lets the formatter place it on the 6-bit CA bus.

### Scheduler interface

`zq_ctrl` presents its calibration request on the carried pair, `zq_req_o`/`zq_grant_i`, alongside refresh's own pair. The scheduler does not special-case ZQ versus refresh; each source waits its turn. See `05_scheduler.md` for the maintenance request/grant table.

## FSM policy

The inherited DDR4 core keeps whatever FSM it already has. This page does not invent a new one for it.

The LPDDR4 MPC submodule is a new small FSM with the four states listed above: `MPC_IDLE`, `MPC_ISSUE`, `MPC_WAIT`, `MPC_DONE`. It is not nested under the DDR4 core; it is a sibling path selected by `MEMTYPE`.

## Timing

For DDR4, `tZQCS` and `tZQCL` are runtime CSRs enforced by the inherited core. For LPDDR4, `tZQ` is a runtime CSR, initialised from the JESD209-4 speed bin at CSR-derivation time (HAS Ch 5; numeric constants are HAS open question Q1), and the MPC submodule waits it out in `MPC_WAIT`.

The interval counter reloads when calibration completes. A mid-interval CSR change takes effect on the next reload, following the same reload-only rule used elsewhere.

## Notes

- **Init-time ZQCL:** the carried core has no init handshake. The init-time long calibration is sequenced by the scheduler macro's `t_zqinit_wait_i` window (and the init MRS/ZQ chain in the macro); this block owns periodic `ZQCS` from `t_zqcs_interval_i`. When the MPC submodule lands it takes over the LPDDR4 side of that chain.
- **Telemetry sharing:** `obs_zqcs_total_o`, `obs_interval_cnt_o`, and `obs_overdue_o` are the core's counters. The MPC submodule will share them when it lands; the two paths never operate at once because the memtype selects one build, so there is no arbitration conflict.
- **Placement policy:** the `overdue_max_i`/`placement_i` policy is inherited for DDR4 and carried conceptually for LPDDR4, but this edition only exercises the default path for LPDDR4 MPC calibration. Future policy hooks use the same CSR surface.
