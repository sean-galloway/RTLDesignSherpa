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

# Power-Down Controller (`powerdown_ctrl`)

**Module:** `powerdown_ctrl.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent macro:** `pumice_mem_cmd_scheduler`
**Status:** Live but optional — a single-channel idle-detect power-down requester. Not instantiated in the default top build. Deep Power Down, per-rank control, and refresh/init interlocks are TODO (see Open Questions).

> **Renamed / rescoped.** An earlier SWAG called this `power_state_fub` and
> described a per-rank FSM array with a separate DEEP_POWER_DOWN state, a
> quiet-point detector, self-refresh coordination handshake with the refresh
> manager, split APD/SRF idleness counters, an init-time CKE handoff mux, and a
> large CSR/IRQ interface. **None of that is implemented.** The actual RTL is a
> single channel-wide 4-state FSM (`S_AWAKE / S_ARMING / S_REQ / S_ASLEEP`) that
> detects controller idleness and requests either Precharge Power Down (PDE) or
> Self Refresh (SR). CKE is dropped for all ranks together. This chapter
> describes what the RTL actually does.

---

## Purpose

`powerdown_ctrl` is a small idle-detector that asks the scheduler for permission
to put the DRAM into a low-power state, then drops the DFI clock-enable (`CKE`)
when granted. It supports two low-power flavors, selected by two enable inputs:

1. **PDE (Precharge Power Down)** — CKE low, banks may stay precharged; wakes on
   any new controller activity.
2. **SR (Self Refresh)** — CKE low while the DRAM self-refreshes internally.
   SR takes priority over PDE when both are enabled.

The FSM only drops and raises `CKE`. It does **not** issue the SREFE/SREFX DRAM
commands, does **not** run any exit-timing counters (tXP / tXSDLL / tXSR), and
does **not** coordinate a handshake with the refresh controller. All command
issue, precondition enforcement (all banks precharged before SR), and exit
timing are the responsibility of the parent scheduler
(`pumice_mem_cmd_scheduler`) — this FUB is purely a request/grant + CKE-drive
block. It trusts the scheduler not to issue a grant before DRAM init completes.

---

## Synthesis Parameters

| Parameter    | Default | Effect                                                                    |
|--------------|---------|---------------------------------------------------------------------------|
| `NUM_RANKS`  | `1`     | Number of ranks. `CKE` is driven identically to all ranks (see below).    |
| `CS_WIDTH`   | `NUM_RANKS` | Width of the `dfi_cke_o` output vector.                                |

There is no `MEMTYPE` parameter and no build-time DPD/PDE/SR selection — the
enable inputs select behavior at run time.

---

## FSM

The block is a **single** channel-wide FSM (`state_e`, 3-bit encoded), not a
per-rank array. There is no separate Deep Power Down state.

| State       | Encoding | Meaning                                              | `dfi_cke_o` |
|-------------|----------|------------------------------------------------------|-------------|
| `S_AWAKE`   | `3'd0`   | CKE high, normal operation; idle counter held at 0   | `'1`        |
| `S_ARMING`  | `3'd1`   | Controller idle; counting cycles toward entry        | `'1`        |
| `S_REQ`     | `3'd2`   | `pdn_req_o` high, awaiting `pdn_grant_i`             | `'1`        |
| `S_ASLEEP`  | `3'd3`   | Granted; CKE low, in PDE or SR per latched `r_kind`  | `'0`        |

Reset state is `S_AWAKE` with `dfi_cke_o = '1` (CKE high out of reset).

### PDE-vs-SR Selection

The request is enabled when either mode is enabled:
`w_request_enabled = enable_pde_i || enable_sref_i`.

- `enable_sref_i` high → on reaching the idle threshold, request **SR**
  (`pdn_kind_o = 1`). SR has priority over PDE.
- `enable_sref_i` low, `enable_pde_i` high → request **PDE** (`pdn_kind_o = 0`).
- Neither enabled → never request; the FSM stays in `S_AWAKE`.

The kind is latched into `r_kind` at the `S_ARMING → S_REQ` transition
(`r_kind <= enable_sref_i`) and is held through `S_ASLEEP`.

### Transitions

```
S_AWAKE:
  r_idle_cnt <- 0
  if (w_request_enabled && controller_idle_i) -> S_ARMING

S_ARMING:
  if (!controller_idle_i || !w_request_enabled) -> S_AWAKE, r_idle_cnt <- 0
  else if (r_idle_cnt >= idle_threshold_i)      -> S_REQ, r_kind <- enable_sref_i
  else                                          r_idle_cnt <- r_idle_cnt + 1

S_REQ:
  if (!controller_idle_i || !w_request_enabled) -> S_AWAKE, r_idle_cnt <- 0
  else if (pdn_grant_i)                         -> S_ASLEEP
                                                   (r_grants_sr++ if r_kind else r_grants_pde++)

S_ASLEEP:
  if (!controller_idle_i)                       -> S_AWAKE, r_idle_cnt <- 0
  // wakes on ANY new activity; SR exit timing (tXSDLL/tXSR) is enforced
  // by the scheduler, not here
```

Any loss of `controller_idle_i` (or de-assertion of both enables) at
`S_ARMING` or `S_REQ` backs the FSM off to `S_AWAKE`. From `S_ASLEEP`, the FSM
wakes on any new controller activity and returns to `S_AWAKE`; the scheduler is
responsible for honoring exit latency before issuing commands to the DRAM.

The grant counters `r_grants_pde` / `r_grants_sr` (16-bit) increment on each
successful grant and are exposed as observability outputs.

### CKE Behavior

`dfi_cke_o` is a strict-flop output: `'1` out of reset and whenever the FSM is
not in `S_ASLEEP`; `'0` in `S_ASLEEP`. `CKE` is `CS_WIDTH`-wide but every bit is
driven identically — the block powers down **all ranks together**. Per-rank CKE
control is a documented TODO.

All outputs are registered (strict-flop), so `pdn_req_o`, `pdn_kind_o`,
`sref_active_o`, `dfi_cke_o`, and the `obs_*` signals lag the internal state by
one cycle.

---

## Interface

Clock `mc_clk`, active-low reset `mc_rst_n`.

### Control / Configuration Inputs

| Signal              | Direction | Width  | Description                                                        |
|---------------------|-----------|--------|--------------------------------------------------------------------|
| `idle_threshold_i`  | input     | 16     | Idle cycles to count in `S_ARMING` before requesting power-down    |
| `enable_pde_i`      | input     | 1      | Enable Precharge Power Down requests                               |
| `enable_sref_i`     | input     | 1      | Enable Self Refresh requests; takes priority over PDE              |
| `controller_idle_i` | input     | 1      | Controller idle indication from the scheduler                     |

### Request / Grant + CKE

| Signal          | Direction | Width      | Description                                              |
|-----------------|-----------|------------|----------------------------------------------------------|
| `pdn_req_o`     | output    | 1          | High while in `S_REQ` (requesting power-down)            |
| `pdn_kind_o`    | output    | 1          | Requested kind: `0` = PDE, `1` = SR                      |
| `pdn_grant_i`   | input     | 1          | Scheduler grant; `S_REQ → S_ASLEEP` on assertion         |
| `sref_active_o` | output    | 1          | High while asleep in SR (`S_ASLEEP && r_kind == 1`)      |
| `dfi_cke_o`     | output    | `CS_WIDTH` | DFI clock-enable; `'0` in `S_ASLEEP`, else `'1`          |

### Observability (future CSR readout)

These outputs are provided for future CSR readback; there is no CSR/APB
interface wired into this FUB today.

| Signal              | Direction | Width | Description                                  |
|---------------------|-----------|-------|----------------------------------------------|
| `obs_state_o`       | output    | 3     | Current FSM state (`state_e` encoding)       |
| `obs_idle_cnt_o`    | output    | 16    | Current idle counter value                   |
| `obs_grants_pde_o`  | output    | 16    | Count of PDE grants taken                    |
| `obs_grants_sr_o`   | output    | 16    | Count of SR grants taken                     |

---

## Verification Notes (cocotb test plan)

The block is small and self-contained; a directed FSM testbench is sufficient.

| Scenario                                                                       | What it proves                                              |
|--------------------------------------------------------------------------------|-------------------------------------------------------------|
| Reset → `S_AWAKE`, `dfi_cke_o = '1`, all `obs_*` cleared                        | Reset behavior and CKE-high default                         |
| Neither enable set; hold idle → FSM never leaves `S_AWAKE`                      | No request when disabled                                    |
| `enable_pde_i` only; idle for `idle_threshold_i` cycles → `pdn_req_o`, `pdn_kind_o = 0` | PDE arming/threshold and request               |
| `enable_sref_i` set (with or without PDE) → `pdn_kind_o = 1`                    | SR priority over PDE                                        |
| `S_REQ` then `pdn_grant_i` → `S_ASLEEP`, `dfi_cke_o = '0`, `sref_active_o` per kind | Grant, sleep, CKE drop, SR-active flag              |
| Activity (`!controller_idle_i`) during `S_ARMING` → back to `S_AWAKE`, counter cleared | Arming back-off                                    |
| Activity during `S_REQ` (before grant) → back to `S_AWAKE`                      | Request withdrawal on new activity                          |
| Wake from `S_ASLEEP` on `!controller_idle_i` → `S_AWAKE`, `dfi_cke_o = '1`      | Wake path                                                   |
| Both enables dropped mid-arming / mid-request → back-off to `S_AWAKE`           | Enable de-assertion handling                                |
| Multiple sleep cycles → `obs_grants_pde_o` / `obs_grants_sr_o` increment correctly | Grant counters                                          |
| `idle_threshold_i = 0` → request on first idle cycle in `S_ARMING`              | Threshold edge case                                         |

---

## Open Questions / Future Work

All of the following are called out in the RTL header comments and are **not**
implemented today:

- **Deep Power Down (DPD).** LPDDR2-only. Would need an `enable_dpd_i` input and
  `dfi_dram_clk_disable_o` cooperation from `dfi_signal_pack`. There is no DPD
  state in the current FSM.
- **Per-rank power-down.** The block currently powers down **all ranks
  together** (identical CKE on every `dfi_cke_o` bit). A per-rank FSM array with
  independent CKE routing is future work.
- **`dfi_init_complete` interlock.** The FSM currently trusts the scheduler not
  to issue `pdn_grant_i` before DRAM init completes. A hard interlock input is
  future work.
- **Self-refresh command / handshake ownership.** SREFE/SREFX command issue,
  the all-banks-precharged precondition, and exit-timing enforcement
  (tXP / tXSDLL / tXSR) live in the scheduler, not here. There is no
  `refresh_ctrl` coordination handshake in this FUB.
- **CSR / observability wiring.** The `obs_*` outputs are intended for future
  CSR readback but are not connected to any APB register block yet.
- **Not in the default top build.** The module is live and verifiable
  standalone, but is not instantiated in the default `pumice` top today.
