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

# Write Leveling Interface (`scoria_wrlvl_ifc`)

**Module:** `scoria_wrlvl_ifc.sv`
**Location:** `rtl/fub/`
**Category:** training control / PHY handshake
**Parent:** `scoria_scheduler_layer`
**Status:** landed and sim-verified

## Purpose

`scoria_wrlvl_ifc` is the controller-side write-leveling interface. It does **not** contain a delay-line search; that is decision D2. The block sequences the DFI v3.1 per-CS leveling handshake, enforces the JESD79-3F timing windows, captures the DRAM's prime-DQ answer, and exposes telemetry so firmware can distinguish four outcomes: never attempted, converged, timed out, and swept with no flip found.

The reasoning behind the no-search rule is the family's architectural boundary. A tap sweep is PHY calibration — step size, tap count, monotonicity, and temperature behavior are PHY properties, not DDR3 properties. Putting the search inside the controller would make a calibration bug a silicon respin instead of a script edit. The block owes the system the handshake, the windows, the capture, and the telemetry; firmware owns the algorithm.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `NUM_CS` | int | 1+ | 1 | number of independent chip selects |
| `CSW` | int | — | `(NUM_CS > 1) ? $clog2(NUM_CS) : 1` | chip-select index width (`cs_sel_i`) |

: Table 2.20.1: Write-leveling interface parameters

## Interface

### Mode and host controls

| Signal | Direction | Width | Description |
|---|---|---|---|
| `wrlvl_en_i` | in | 1 | DRAM is in write-leveling mode (from `scoria_mode_register.wrlvl_en_o`) |
| `strobe_i` | in | 1 | host pulse: emit one DQS edge |
| `cs_sel_i` | in | `CSW` | chip select under training |

: Table 2.20.2: Mode and host controls

### Timing windows (runtime CSRs)

| Signal | Direction | Width | Description |
|---|---|---|---|
| `t_wldqsen_i` | in | 16 | `tWLDQSEN`: wait before DQS may be driven |
| `t_wlmrd_i` | in | 16 | `tWLMRD`: wait before the first DQS pulse |
| `t_wlmrd_max_i` | in | 16 | controller-defined `tWLMRD` timeout; `0` = no timeout |
| `t_wlo_i` | in | 16 | `tWLO`: result-return delay after DQS edge |
| `t_wloe_i` | in | 16 | `tWLOE`: inert in this implementation; samples prime DQ only |

: Table 2.20.3: Write-leveling timing CSR inputs

### DFI v3.1 per-CS leveling handshake

| Signal | Direction | Width | Description |
|---|---|---|---|
| `dfi_phylvl_req_cs_n_o` | out | `NUM_CS` | controller requests per-CS write leveling, active low |
| `dfi_phylvl_ack_cs_n_i` | in | `NUM_CS` | PHY acknowledges per CS, active low |
| `dfi_phy_wrlvl_cs_n_o` | out | `NUM_CS` | selects write leveling per CS, active low |
| `dfi_wrlvl_strobe_o` | out | 1 | DQS strobe forwarded by the PHY for the prime-DQ sample |

: Table 2.20.4: DFI v3.1 write-leveling handshake

### DRAM answer and telemetry

| Signal | Direction | Width | Description |
|---|---|---|---|
| `prime_dq_i` | in | 1 | sampled prime DQ returned by the PHY |
| `result_valid_o` | out | 1 | a sample completed |
| `result_o` | out | 1 | captured prime-DQ value |
| `obs_attempts_o` | out | 16 | number of strobes emitted |
| `obs_flips_o` | out | 16 | result-bit transitions observed across the sweep |
| `obs_timeout_o` | out | 1 | `t_wlmrd_max_i` expired |
| `obs_ever_done_o` | out | 1 | a pass has completed at least once |
| `obs_state_o` | out | 3 | FSM-state observability |

: Table 2.20.5: DRAM answer and host telemetry

The telemetry discipline is the four-state story: reset is never-attempted, `obs_ever_done_o` marks converged, `obs_timeout_o` marks timed out, and a completed sweep with `obs_flips_o == 0` marks no result in window. The counters survive `wrlvl_en_i` going low so firmware can read the record of the pass that just finished.

## Microarchitecture internals

### FSM state list

```text
WL_OFF
WL_DQSEN
WL_MRD
WL_READY
WL_WAIT_WLO
WL_TIMEOUT
```

### State behavior

```text
WL_OFF      -> WL_DQSEN      when wrlvl_en_i rises
WL_DQSEN    -> WL_MRD        after tWLDQSEN
WL_MRD      -> WL_READY      after tWLMRD
WL_READY    -> WL_WAIT_WLO   on strobe_i
WL_READY    -> WL_TIMEOUT    if t_wlmrd_max_i expires with no strobe
WL_WAIT_WLO -> WL_READY      after tWLO, result captured
WL_TIMEOUT  -> WL_TIMEOUT    sticky until wrlvl_en_i clears
```

`dfi_wrlvl_strobe_o` is generated only in `WL_READY` and only when `strobe_i` is high. A strobe arriving early is dropped, not deferred; deferring would report an attempt the DRAM never saw.

### `t_wlmrd_max_i` timeout behavior

The timeout is armed when `t_wlmrd_max_i != 0`. It measures elapsed time since entering write-leveling mode, but it restarts on every accepted strobe. Without the restart, a host sweeping delay taps would blow through any sensible timeout part-way through a working pass and get `WL_TIMEOUT` spuriously.

### DFI handshake outputs

`dfi_phylvl_req_cs_n_o` and `dfi_phy_wrlvl_cs_n_o` are driven active-low on the selected chip select for as long as `wrlvl_en_i` is high, and driven high (inactive) otherwise. The one-hot decode guards against `cs_sel_i` values past `NUM_CS`.

## FSM policy

The block has one minimal window-sequencer FSM. There are no search states, no delay-walk states, and no tap-storage registers. The host walks the delay line by asserting `strobe_i` again with a new delay setting.

## Timing

| Window | Symbol | Source | Meaning |
|---|---|---|---|
| `tWLDQSEN` | `t_wldqsen_i` | JESD79-3F | wait after entering leveling mode before driving DQS |
| `tWLMRD` | `t_wlmrd_i` | JESD79-3F | wait before the first DQS pulse |
| `tWLMRD` max | `t_wlmrd_max_i` | controller-defined | timeout with distinct status |
| `tWLO` | `t_wlo_i` | JESD79-3F speed bin | result-return delay after DQS edge |
| `tWLOE` | `t_wloe_i` | JESD79-3F speed bin | inert: bounds mismatch across DQ bits, but only the prime bit is sampled |

: Table 2.20.6: Write-leveling timing windows

All values are runtime CSRs, initialized from the JESD79-3F speed bin at CSR-derivation time.

## Notes

- **No on-chip tap search.** This is decision D2 and is the defining boundary of the block. A future system that needs autonomous leveling should add an external calibration engine driving this interface, not a search loop inside `scoria_wrlvl_ifc`.
- **`tWLOE` is inert.** The implementation samples the prime DQ bit only, so `tWLOE` exists in the CSR map for compatibility but does not gate the result capture. That choice is explicit and documented, not an accident.
- **The timeout status is distinct from "no flip found."** `obs_timeout_o` means the host stopped strobing before `t_wlmrd_max_i` elapsed. A sweep that completed but saw zero transitions is `obs_ever_done_o` high, `obs_timeout_o` low, and `obs_flips_o` zero.
- **Cleared only by reset.** `obs_attempts_o`, `obs_flips_o`, `obs_timeout_o`, and `obs_ever_done_o` are not cleared when `wrlvl_en_i` falls; they are cleared only by controller reset. That preserves the record of the pass for firmware inspection.
