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

# ZQ Calibration Controller (`andesite_zq_ctrl`)

**Module:** `andesite_zq_ctrl.sv` + `andesite_zq_mpc_lpddr4.sv` (both landed)
**Location:** `rtl/fub/`
**Category:** maintenance / calibration
**Parent:** `andesite_core`
**Status:** DDR4 core carried from scoria and landed; the LPDDR4 MPC submodule is landed per the FSM below; ports tables reconciled to the landed port lists

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
| `memtype_i` | in | 3 | `memtype_e`: selects the calibration path — `MEMTYPE_LPDDR4` hands expiries to the MPC submodule; anything else runs the inherited DDR4 core |
| `t_zqcs_interval_i` | in | 32 | calibration interval, runtime CSR; 0 = off (shared by both paths) |
| `t_zqcs_i` | in | 16 | `tZQCS` recovery, runtime CSR (DDR4 path) |
| `placement_i` | in | 2 | placement policy select (Mode C, DDR4 path) |
| `overdue_max_i` | in | 13 | defer-under-demand threshold (DDR4 path) |
| `demand_i` | in | 1 | demand indication from the scheduler side |
| `zq_req_o` | out | 1 | request to the scheduler; held until `zq_grant_i` — request-and-wait, never preempt (muxed between the core and the submodule) |
| `zq_grant_i` | in | 1 | scheduler grant |
| `obs_busy_o` | out | 1 | a calibration is in flight (post-grant window, either path) |
| `obs_zqcs_total_o` | out | 16 | issued-calibration counter (shared: counts either path's completion) |
| `obs_interval_cnt_o` | out | 32 | interval countdown observability (shared by both paths) |
| `obs_overdue_o` | out | 1 | overdue flag (DDR4 placement-policy telemetry; the LPDDR4 path does not defer, so it stays low there) |

The carried DDR4 core exposes no DDR4-only ports beyond this set: `ZQCS` is its only calibration flavour, and the init-time long calibration is sequenced by the scheduler macro's `t_zqinit_wait_i` window, not by this block. The original spec sketch's `init_zqcl_req`/`init_zqcl_done` handshake and the unified `maint_req`/`maint_tag` channel are not how the carried RTL works — the core requests calibration on `zq_req_o` and waits on `zq_grant_i`.

### LPDDR4-only ports (the landed MPC submodule)

The submodule is `andesite_zq_mpc_lpddr4` (its own FUB file); `zq_ctrl` instantiates it and memtype-muxes the scheduler pair and the busy observable — a combinational passthrough of the two registered sources, so each path keeps single-register latency.

| Signal | Direction | Width | Description |
|---|---|---|---|
| `t_zq_i` | in | 16 | `tZQ` calibration latency, runtime CSR (JESD209-4 speed-bin derived); waited out in `MPC_WAIT` |
| `mpc_opcode_i` | in | 6 | MPC opcode **image** from the CSR. The encodings are TBC(JESD209-4): the submodule drives the image and never decodes it — no MPC opcode encodings are invented anywhere in andesite |
| `mpc_issuing_o` | out | 1 | high in `MPC_ISSUE`; the formatter samples the image with the grant cycle |
| `mpc_op_o` | out | 6 | the opcode image presented while issuing (follows `mpc_opcode_i` combinationally) |

: Table 2.7.2: ZQ controller ports

## Microarchitecture internals

### DDR4 path: inherited from scoria

The DDR4 core is scoria's `zq_ctrl`, unchanged. It implements:

- Interval CSR: countdown to the next calibration event.
- Request-and-wait grant: it asks the scheduler and waits; it never preempts.
- `tZQCS` enforcement: the next interval is held until the recovery time expires.
- Issued-calibration counter: tracks how many calibrations have gone out.
- CSR-selectable placement policy: scoria TASK-001 Mode C, baseline versus defer-under-demand with `overdue_max`.

For the internal details, see scoria's HAS Ch 3.2 and the landed RTL in `projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/zq/`. This MAS page does not re-specify what already exists; it cites it.

### LPDDR4 path: new MPC submodule

LPDDR4 carries calibration on the MPC command, not dedicated `ZQCS`/`ZQCL` opcodes. The new submodule issues the ZQCal start and ZQCal latch opcodes through the formatter's LPDDR4 CA submodule.

```text
MPC_IDLE
    -> MPC_ISSUE   (assert cmd_req, wait for scheduler grant, drive MPC ZQCal start)
    -> MPC_WAIT    (wait tZQ latched from CSR)
    -> MPC_DONE    (drive calibration complete, reload interval counter)
    -> MPC_IDLE
```

`tZQ` here is the LPDDR4 ZQ calibration latency, the `t_zq_i` runtime CSR loaded from JESD209-4 at CSR-derivation time. The submodule rides the core's shared interval counter and telemetry: `obs_zqcs_total_o` counts either path's completion, `obs_interval_cnt_o` is the live countdown, and `MPC_DONE` is what reloads the shared interval.

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
