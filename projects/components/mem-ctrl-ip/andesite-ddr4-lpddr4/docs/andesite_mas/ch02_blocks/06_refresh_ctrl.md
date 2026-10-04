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

# Refresh Controller (`andesite_refresh_ctrl`)

**Module:** `andesite_refresh_ctrl.sv`
**Location:** `rtl/refresh/`
**Category:** maintenance / refresh
**Parent:** `andesite_core`
**Status:** specified — no RTL exists (HAS v0.1 posture)

---

## Purpose

`refresh_ctrl` keeps the DRAM rows alive. It inherits scoria's verified base, specified in `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/docs/scoria_has/ch03_architecture/04_refresh.md` and proven in `formal/scoria/refresh_ctrl`: the `tREFI` interval counter, all-bank refresh, JEDEC's plus-or-minus-eight postpone/pull-in credit window, and the TASK-001 policy modes (A: elastic refresh, B: temperature-compensated refresh, C: placement discipline). The andesite deltas are DDR4 fine-granularity refresh and LPDDR4 controller-directed per-bank refresh.

The block is MODIFIED, not rewritten. Every inherited property transfers with the mechanism.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `NUM_BANKS` | int | 8..16 | 16 for DDR4, 8 for LPDDR4 | banks per rank |
| `FGR_SUPPORTED` | bit | 0,1 | 1 | when 1, the FGR factor CSR is active |
| `REFPB_SUPPORTED` | bit | 0,1 | 1 for LPDDR4, 0 for DDR4 | enables per-bank refresh path |

: Table 2.6.1: Refresh controller parameters

## Interface

| Signal | Direction | Width | Description |
|---|---|---|---|
| `clk` | in | 1 | controller clock |
| `reset_n` | in | 1 | active-low reset |
| `trefi_csr` | in | timing width | `tREFI`, runtime CSR |
| `tfgr_1x_csr` | in | timing width | `tRFC` for 1x refresh, runtime CSR |
| `tfgr_2x_csr` | in | timing width | `tRFC` for 2x refresh, runtime CSR |
| `tfgr_4x_csr` | in | timing width | `tRFC` for 4x refresh, runtime CSR |
| `fgr_factor_csr` | in | 2 | `1x`, `2x`, or `4x` FGR select from MR3 image |
| `perbank_policy_csr` | in | 2 | LPDDR4 per-bank policy; reset to round-robin |
| `maint_req` | out | 1 | request to scheduler |
| `maint_grant` | in | 1 | scheduler grant |
| `maint_tag` | out | `MAINT_TAG_WIDTH` | `MAINT_REF` |
| `refresh_bank` | out | bank width | bank address for LPDDR4 per-bank refresh |
| `refresh_all` | out | 1 | high for DDR4 all-bank `REF` |
| `bank_busy_in` | in | `NUM_BANKS` | bank timer busy mask |
| `csr_mode_a_en` | in | 1 | elastic refresh enable |
| `csr_pullin_idle_streak` | in | 5..8 | Mode A pull-in idle confirmation |
| `csr_postpone_demand_streak` | in | 5..8 | Mode A postpone demand streak |
| `csr_tcr_en` | in | 1 | temperature-compensated refresh enable |
| `csr_trefi_derate` | in | 2 | Mode B derate factor |
| `ref_stats_postpone` | out | 32 | postpone event count |
| `ref_stats_pullin` | out | 32 | pull-in event count |
| `ref_stats_fgr_factor` | out | 2 | current FGR factor |
| `ref_stats_perbank_bank` | out | bank width | last per-bank refresh target |

: Table 2.6.2: Refresh controller ports

## Microarchitecture internals

### Inherited mechanism

The base mechanism is scoria's `refresh_ctrl`, proven in `formal/scoria/refresh_ctrl`. It carries:

- A `tREFI` interval counter.
- The JEDEC ±8 postpone/pull-in credit window.
- Mode A elastic streaks: `pullin_idle_streak` reset to 16, `postpone_demand_streak` reset to 1.
- Mode B TCR derate applied to the counter reload only.
- `REF_STATS` telemetry.
- The sixteen-cycle idle confirmation, because CAM occupancy blinks off between bursts and those micro-gaps must not be treated as idle.

The credit ceiling is ±8 in every mode. Mode A and Mode B touch scheduling policy, not the credit arithmetic.

### DDR4 delta: fine-granularity refresh

DDR4's MR3 selects 1x, 2x, or 4x refresh granularity. The controller scales its interval arithmetic by the FGR factor.

```text
fgr_factor = {1x:1, 2x:2, 4x:4}   (MR3 image, runtime CSR)
tREFI_effective = tREFI / fgr_factor   (counter reload value)
tRFC_active = tRFC(fgr)                 (CSR per density)
credits window scales with the density bookkeeping — the ±8 ceiling is unchanged.
```

`fgr_factor_csr` is the runtime copy of the MR3 field that `init_sequencer` programmed. The `tREFI` counter reloads with `tREFI_effective`. The per-refresh busy window uses `tRFC_active`, selected from the `tfgr_1x_csr`, `tfgr_2x_csr`, or `tfgr_4x_csr` register based on the factor.

The credit-window bookkeeping scales with the density accounting, but the ±8 ceiling is unchanged. Postponing 8 refreshes at 4x granularity is not the same as postponing 8 refreshes at 1x; the bookkeeping must track effective refreshes, not raw commands.

### LPDDR4 delta: controller-directed per-bank refresh

LPDDR4 changes who names the bank. For LPDDR2/3, `REFpb` carried no bank address and scoria's rotor mirrored the device's fixed counter. JESD209-4 lets the controller put the bank on the CA bus, so the rotor is replaced by explicit bank scheduling.

This edition implements a round-robin default. The policy layer that scoria's TASK-001 built — CSR-select, reset-off, telemetry-instrumented — is exactly where occupancy-aware schemes from andesite TASK-001's DARP survey would hang. Round-robin is the commodity choice; advanced schemes are left as future policy hooks.

The scheduling policy hook is a small module that picks the next bank. It receives the bank busy mask and the current per-bank pointer, and produces `refresh_bank`. Round-robin advances the pointer to the next non-busy bank. Future policies can replace this module without touching the refresh engine.

## FSM policy

The refresh engine's FSM is inherited in shape: request/grant, issue, then track the busy interval. The FGR factor and per-bank selection are inputs, not new states.

Mode selects are data, not control. Whether the current refresh is 1x or 4x, all-bank or per-bank, round-robin or occupancy-aware — these choices change the values loaded into counters and the bank address driven to the scheduler. They do not change the state machine's skeleton. That's why the FSM stays inherited.

## Timing

The `tREFI` counter reloads with `tREFI_effective`, a runtime CSR derived from the JESD79-4/JESD209-4 speed bin at CSR-derivation time (HAS Ch 5; numeric constants are HAS open question Q1). `tRFC_active` is selected from the FGR-specific CSR.

The Mode B TCR derate applies to the reload value only: a mid-interval CSR change takes effect on the next reload, not on the running counter. That's the same reload-only rule inherited from scoria.

## Notes

- **Formal obligation:** Retention must be re-derived per FGR factor and for the per-bank arithmetic. Carrying the 1x all-bank proof forward unchanged would prove the wrong thing while appearing green. The obligation is recorded here and in HAS Ch 6 item 5.
- **Refresh is an ordinary bank occupant:** Bank timers own the banks during refresh. A refresh request is not a special bypass; it waits its turn in the scheduler like any other command.
- **Why round-robin only:** Occupancy-aware per-bank refresh is implementable now that the controller names the bank, but it is a policy change, not a mechanism change. The policy hook exists; the survey's schemes stay in andesite TASK-001.
- **Telemetry:** `REF_STATS` carries over. `ref_stats_fgr_factor` and `ref_stats_perbank_bank` join it so a refresh sweep is measurable in-system rather than inferred.
