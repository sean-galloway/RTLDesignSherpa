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

# Init Sequencer (`andesite_init_sequencer`)

**Module:** `andesite_init_sequencer.sv`
**Location:** `rtl/init/`
**Category:** control / initialization
**Parent:** `andesite_core` / `andesite_top`
**Status:** specified — no RTL exists (HAS v0.1 posture)

---

## Purpose

`init_sequencer` owns the power-up handshake with the DRAM. It drives `RESET#`, raises `CKE`, programs the mode-register set in JEDEC order, issues `ZQCL`, waits out `tDLLK` and `tZQinit`, and optionally performs the gear-down entry sequence. Until it reaches `READY`, the sequencer holds the command bus: no host traffic reaches the formatter. After `READY`, it goes idle but stays available for a firmware-triggered re-initialization.

The block is MODIFIED from scoria because DDR4 adds the `RESET#` pin, seven mode registers, gear-down, and CA parity enable; LPDDR4 needs its own bus-reset, MRW order, and MPC-carried calibration handoff.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `MEMTYPE` | `memtype_e` | `DDR4`, `LPDDR4` | build | selects the init branch and the MR set |
| `NUM_CHANNELS` | int | 1..2 | 1 | LPDDR4 channel count; DDR4 uses 1 |
| `GEARDOWN_SUPPORTED` | bit | 0,1 | 1 | when 1, the FSM includes the gear-down entry states |

: Table 2.2.1: Init sequencer build parameters

All timing values are runtime CSRs, not parameters. That's the family rule: a timing compiled in cannot be swept, and a controller that cannot be swept cannot be characterized.

## Interface

| Signal | Direction | Width | Description |
|---|---|---|---|---|
| `clk` | in | 1 | controller clock |
| `reset_n` | in | 1 | active-low reset |
| `csr_init_trigger` | in | 1 | firmware pulse: drop back to `POWER_ON_RESET` and re-run |
| `csr_memtype` | in | 3 | runtime copy of `MEMTYPE` for the FSM branch |
| `csr_geardown_en` | in | 1 | enable gear-down entry after `ZQCL` |
| `csr_parity_en` | in | 1 | enable CA parity through the MR sequence |
| `tinit1_csr` | in | `TINIT_WIDTH` | `tINIT1` wait, runtime CSR |
| `tinit3_csr` | in | `TINIT_WIDTH` | `tINIT3` wait, runtime CSR |
| `tinit4_csr` | in | `TINIT_WIDTH` | `tINIT4` wait, runtime CSR |
| `tdllk_csr` | in | `TINIT_WIDTH` | `tDLLK` wait, runtime CSR |
| `tzqinit_csr` | in | `TINIT_WIDTH` | `tZQinit` wait, runtime CSR |
| `tmrd_csr` | in | `TINIT_WIDTH` | `tMRD` wait, runtime CSR |
| `tmod_csr` | in | `TINIT_WIDTH` | `tMOD` wait, runtime CSR |
| `mr_image_out` | out | packed MR vector | current MR value for `mode_register` |
| `mr_load` | out | 1 | pulse: `mode_register` captures `mr_image_out` |
| `reset_n_out` | out | 1 | `RESET#` pin to top/PHY, active low |
| `cke_out` | out | 1 | `CKE` pin, registered from activation until init complete |
| `cmd_req` | out | 1 | request to the formatter/scheduler for the next init command |
| `cmd_ack` | in | 1 | grant: the command is issued this cycle |
| `cmd_op` | out | opcode | init command opcode (MRS/MRW/ZQCL/MPC/etc.) |
| `cmd_bank` | out | 3 | bank address (2 bits used); the MRS path carries the 3-bit MR index (0-6) |
| `cmd_addr` | out | address width | MR index / MRW address field |
| `zq_cal_start` | out | 1 | pulse to `zq_ctrl` to start ZQ calibration |
| `gear_down_entry` | out | 1 | pulse to PHY/formatter to enter gear-down `§TBC(TASK-005)` |
| `parity_enable_out` | out | 1 | parity is now active; formatter begins counting |
| `init_done` | out | 1 | `READY` reached, normal operation may begin |
| `init_err` | out | 1 | sequencing or timeout error, latched until re-init |
| `ca_train_start` | out | 1 | LPDDR4 handoff to `ca_train_ifc` when training is required |
| `parity_alert_i` | in | 1 | the formatter's logged CA-parity alert pulse; the recovery FSM's entry event |
| `recovery_interval_i` | in | 16 | JEDEC-named recovery interval for `RESENDING`, runtime CSR |
| `csr_telem_clear_i` | in | 1 | explicit firmware clear of the recovery telemetry |
| `retract_req_o` | out | 1 | maintenance-class request asking the scheduler to withdraw the suspect command |
| `retract_ack_i` | in | 1 | scheduler grant for the retract; request-and-wait, like `cmd_req`/`cmd_ack` |
| `obs_recovery_state_o` | out | 2 | recovery sub-FSM state: 0 `IDLE`, 1 `ALERT_SEEN`, 2 `RESENDING` |
| `obs_alerts_seen_o` | out | 16 | saturating telemetry: alerts seen |
| `obs_cmds_dropped_o` | out | 16 | saturating telemetry: suspect commands dropped |
| `obs_cmds_resent_o` | out | 16 | saturating telemetry: commands released for re-issue |

: Table 2.2.2: Init sequencer ports

The `cmd_req`/`cmd_ack` pair is the same request-and-wait discipline the scheduler uses for maintenance traffic. Init owns the bus, but it still waits for the formatter to be ready.

## Microarchitecture internals

### DDR4 FSM state sequence

The DDR4 branch is one flat FSM. Gear-down entry is folded as states, not a nested machine.

```text
POWER_ON_RESET
    -> RESET_ASSERT        (drive RESET# low; wait tINIT1)
    -> RESET_DEASSERT_WAIT  (RESET# high; wait tINIT3)
    -> CKE_ENABLE           (raise CKE)
    -> CKE_WAIT            (wait tINIT4)
    -> MRS_MR3
    -> MRS_MR6
    -> MRS_MR5
    -> MRS_MR4
    -> MRS_MR2
    -> MRS_MR1
    -> MRS_MR0
    -> ZQCL
    -> DLLK_ZQINIT_WAIT    (wait tDLLK and tZQinit)
    -> [GEARDOWN_ENTRY if csr_geardown_en: program MR3 gear-down,
        issue entry sequence, wait sync]
    -> READY
```

### LPDDR4 FSM state sequence

LPDDR4 uses its own branch. The exact MRW order follows JESD209-4; the table below captures the structural stages.

```text
POWER_ON_RESET
    -> BUS_RESET            (reset over CA bus or reset pin per JESD209-4)
    -> INIT_WAIT            (JESD209-4 initialization wait)
    -> MRW_SEQUENCE        (JESD209-4 order: device feature, ODT,
                            drive-strength, DQ-ODT, and remaining MRs)
    -> MPC_ZQ_CALIBRATION  (issue MPC ZQCal start / latch via formatter CA path)
    -> [CA_TRAINING_HANDOFF if required: ca_train_start to ca_train_ifc]
    -> READY
```

### Sequencing rules

The MR order is a citation, not a design choice. pumice's EMRS3-first correction is the family precedent, and andesite follows it: MR3 first, then MR6, MR5, MR4, MR2, MR1, MR0 last. MR0 carries the DLL reset only; CA parity latency/mode is programmed in MR5, so parity enable rides the MR5 program step. MR0 must wait until the bus is stable.

Parity enable is ordered after bus stability for the same reason. Once `parity_enable_out` rises, the formatter's parity counter starts counting from that point; enabling it earlier would count commands that were not parity-protected.

`CKE` is continuously registered from the `CKE_ENABLE` state until init completes. Dropping it mid-sequence is an error and is flagged by `init_err`.

## FSM policy

This block has **one FSM** and it is the init FSM. There are no nested FSMs and no sub-state machines hidden inside the MR sequence. Gear-down entry is a sequence of states in the same FSM; the PHY/formatter handshake is a single output pulse plus a wait state.

The MR states themselves are simple: load the next MR image, pulse `mr_load`, assert `cmd_req`, wait for `cmd_ack`, then wait `tMRD` or `tMOD` as required before the next state.

## Timing

Every wait state counts from a CSR-loaded value. The values are runtime CSRs, initialised from the JESD79-4/JESD209-4 speed bin at CSR-derivation time (HAS Ch 5; numeric constants are HAS open question Q1).

| Wait | Symbol | Loaded from | Counted in |
|---|---|---|---|
| Reset assertion | `tINIT1` | `tinit1_csr` | MC clocks |
| Reset deassert to CKE | `tINIT3` | `tinit3_csr` | MC clocks |
| CKE to first MRS/MRW | `tINIT4` | `tinit4_csr` | MC clocks |
| Between MRS commands | `tMRD` | `tmrd_csr` | MC clocks |
| MRS to non-MRS command | `tMOD` | `tmod_csr` | MC clocks |
| DLL lock + ZQ init | `tDLLK`, `tZQinit` | `tdllk_csr`, `tzqinit_csr` | MC clocks, both must expire |

The counter reload value for each state is captured when the state is entered, so a CSR written mid-wait does not affect the running count. That's the same reload-only rule the refresh controller uses for `tREFI` derate.

Ordering checks — for example, that MR3 is issued before MR0 — are assertions in DV, not in RTL. That's the family rule: the FSM encodes the order, and DV proves the FSM never strays.

## Notes

- **LPDDR4 calibration handoff:** `MPC_ZQ_CALIBRATION` does not perform the calibration itself. It issues the MPC opcodes through the formatter's LPDDR4 CA submodule and then raises `init_done`. If the board requires CA training, the FSM can hand off to `ca_train_ifc` before `READY`.
- **Re-initialization:** A firmware pulse on `csr_init_trigger` forces the FSM back to `POWER_ON_RESET`. The `init_done` output falls immediately so the scheduler stops admitting host commands.
- **Gear-down and parity are independent CSR selects.** Either, both, or neither may be enabled; the FSM states exist for both paths.
- **DFI 4.0 gear-down handshake:** The `gear_down_entry` pulse crosses to the PHY through the DFI 4.0 control surface `§TBC(TASK-005)`. The exact DFI signal names are public and live in the formatter chapter.

## CA parity error recovery

Recovery from a CA parity alert is handled by a small sub-FSM that sits beside the init FSM and never enters the bank machine. The formatter logs the raw `dfi_alert_n` pulse (see `ch02_blocks/01_cmd_formatter.md` §"CA parity"); that logged pulse is the entry event for this recovery FSM. DFI 4.0 alert and parity semantics are `§3.5.7` and `§4.11`.

```text
IDLE -> ALERT_SEEN -> RESENDING -> IDLE
```

* `IDLE` — waiting. The recovery FSM is transparent; normal scheduler grants pass through unchanged.
* `ALERT_SEEN` — on the cycle the formatter's logged pulse arrives, the command currently in the grant stream is marked suspect and dropped. The FSM asserts a `retract` sideband to the scheduler, asking it to withdraw the suspect command and re-issue it from its request queue. The scheduler's request-never-preempts rule is preserved: the recovery request is just another maintenance-class request that must wait for the scheduler's grant, exactly like the init sequencer's `cmd_req`/`cmd_ack` pair.
* `RESENDING` — after the JEDEC-named recovery interval has elapsed, the recovery FSM re-issues the dropped command through the same formatter path. The interval value is a runtime CSR loaded from the JESD79-4 speed bin at CSR-derivation time; no numeric constant is compiled into the RTL.

Telemetry is kept in small saturating counters: alerts seen, commands dropped, and commands re-issued. These counters are visible to firmware and are reset only by controller reset or an explicit firmware clear.

The recovery FSM does **not** trigger a full re-initialization. A single parity event drops one command and retransmits it; only a sustained or uncorrectable pattern would escalate to firmware-assisted MR5 re-programming or init re-run. That escalation policy is recorded as open question Q4 in the HAS, not hard-wired here.

## Gear-down programming (P1 interpretation, 2026-10-04)

The fence's "program MR3 gear-down" step rides the MR image: the FSM issues
the normal MR3 MRS with whatever image firmware configured
(`csr_mr3_image`), then the entry pulse and the sync wait follow ZQ-init.
The gear-down bit's position in MR3 is Q1 (JESD79-4 cold-storage read) --
the RTL makes no bit-position claim; the P1 test asserts the configured bit
reaches the bus, wiring-only.
