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

**Module:** `andesite_zq_ctrl.sv` + `zq_ctrl_mpc_lpddr4.sv`
**Location:** `rtl/zq/`
**Category:** maintenance / calibration
**Parent:** `andesite_core`
**Status:** specified — no RTL exists (HAS v0.1 posture)

---

## Purpose

`zq_ctrl` issues periodic ZQ calibration. For DDR4, the block is scoria's module carried unchanged: interval CSR, request-and-wait grant, `tZQCS` enforced by holding the next interval, issued-calibration counter, and CSR-selectable placement policy. For LPDDR4, calibration moves onto the MPC command, so a new submodule sequences it through the formatter's LPDDR4 CA path.

The DDR4 side is INHERITED. The LPDDR4 side is NEW. Both share one maintenance request port to the scheduler with a source tag.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `MEMTYPE` | `memtype_e` | `DDR4`, `LPDDR4` | build | selects the active calibration path |
| `ZQ_INTERVAL_WIDTH` | int | 16..32 | 24 | width of the ZQ interval counter |
| `OVERDUE_MAX_WIDTH` | int | 8..16 | 12 | width of the overdue counter for placement policy |

: Table 2.7.1: ZQ controller parameters

## Interface

### Common ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `clk` | in | 1 | controller clock |
| `reset_n` | in | 1 | active-low reset |
| `init_zqcl_req` | in | 1 | from `init_sequencer`: issue ZQCL at init time |
| `init_zqcl_done` | out | 1 | ZQCL complete, init may proceed |
| `maint_req` | out | 1 | request to scheduler |
| `maint_grant` | in | 1 | scheduler grant |
| `maint_tag` | out | `MAINT_TAG_WIDTH` | `MAINT_ZQ` |
| `zq_interval_csr` | in | `ZQ_INTERVAL_WIDTH` | calibration interval, runtime CSR |
| `zq_overdue_max_csr` | in | `OVERDUE_MAX_WIDTH` | placement-policy threshold, runtime CSR |
| `zq_stats_issued` | out | 32 | total calibrations issued |
| `zq_stats_overdue` | out | 32 | calibrations deferred under demand |

### DDR4-only ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `zq_short` | out | 1 | high for `ZQCS`, low for `ZQCL` |
| `tzqcs_csr` | in | timing width | `tZQCS` recovery, runtime CSR |

### LPDDR4-only ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `mpc_zq_start` | out | 1 | issue MPC ZQCal start |
| `mpc_zq_latch` | out | 1 | issue MPC ZQCal latch |
| `mpc_op` | out | 6 | MPC opcode driven to formatter CA submodule |
| `mpc_done` | in | 1 | formatter acknowledges MPC command issued |

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

`tZQ` here is the LPDDR4 ZQ calibration latency, a runtime CSR loaded from JESD209-4 at CSR-derivation time. The submodule shares `zq_stats_issued` and `zq_stats_overdue` with the inherited core so telemetry is one counter set regardless of memtype.

The MPC submodule depends on the LPDDR4 CA path in `dfi_cmd_formatter` (Ch 2.1). It does not build its own CA encoder; it drives the MPC opcode and lets the formatter place it on the 6-bit CA bus.

### Scheduler interface

Whether DDR4 or LPDDR4, `zq_ctrl` presents one maintenance source with the `MAINT_ZQ` tag. The scheduler sees a single `maint_req`/`maint_grant` pair and a tag; it does not special-case ZQ versus refresh or ODT turnarounds. See `05_scheduler.md` for the maintenance request/grant table.

## FSM policy

The inherited DDR4 core keeps whatever FSM it already has. This page does not invent a new one for it.

The LPDDR4 MPC submodule is a new small FSM with the four states listed above: `MPC_IDLE`, `MPC_ISSUE`, `MPC_WAIT`, `MPC_DONE`. It is not nested under the DDR4 core; it is a sibling path selected by `MEMTYPE`.

## Timing

For DDR4, `tZQCS` and `tZQCL` are runtime CSRs enforced by the inherited core. For LPDDR4, `tZQ` is a runtime CSR, initialised from the JESD209-4 speed bin at CSR-derivation time (HAS Ch 5; numeric constants are HAS open question Q1), and the MPC submodule waits it out in `MPC_WAIT`.

The interval counter reloads when calibration completes. A mid-interval CSR change takes effect on the next reload, following the same reload-only rule used elsewhere.

## Notes

- **Init-time ZQCL:** At initialization, `init_sequencer` pulses `init_zqcl_req`. The DDR4 core issues `ZQCL`; the LPDDR4 MPC submodule issues the equivalent MPC ZQCal sequence. When `init_zqcl_done` rises, init proceeds to `DLLK_ZQINIT_WAIT`.
- **Telemetry sharing:** `zq_stats_issued` and `zq_stats_overdue` are shared registers. The DDR4 core and LPDDR4 submodule never operate at the same time because `MEMTYPE` is build-time, so there is no arbitration conflict.
- **Placement policy:** The `zq_overdue_max_csr` policy is inherited for DDR4 and carried conceptually for LPDDR4, but this edition only exercises the round-robin/default path for LPDDR4 MPC calibration. Future policy hooks use the same CSR surface.
