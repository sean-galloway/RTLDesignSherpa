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

# Training Interfaces (`andesite_wrlvl_ifc`, `andesite_rdlvl_ifc`, `andesite_ca_train_ifc`)

**Module:** `andesite_wrlvl_ifc` (MODIFIED), `andesite_rdlvl_ifc` (NEW), `andesite_ca_train_ifc` (NEW)
**Location:** `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/`
**Category:** training control / PHY handshake
**Parent:** `andesite_top` / DFI boundary
**Status:** specified — no RTL exists (HAS v0.1 posture)

## Purpose

These three blocks expose DRAM training as controller-side sequencing
engines. They handle the DFI handshake, the mode-register or MPC path, the
JEDEC timing windows, and the result capture. The actual delay-line search
lives in firmware — the controller provides the interface, not the algorithm.
This page collects the family because all three share the same handshake
discipline, the same telemetry framing, and the same no-search rule.

### The three family rules

1. **No search loop in hardware.** Anywhere. The blocks handshake, sequence,
   window, and report; firmware walks the delays.
2. **Four-state telemetry.** The host must distinguish never attempted,
   converged, timed out, and no result in window. A detector that has never
   fired is not evidence of anything — that's the pumice CRC lesson, and this
   family applies it to training.
3. **CSR-defined timeouts with distinct status.** Where a JEDEC window's
   maximum is controller-dependent, the CSR defines it with a distinct status
   bit. A host that waits forever for a result it will never get looks the
   same as a broken link.

## Parameters

| Parameter | Type | Range | Default | Meaning | PRD |
|---|---|---|---|---|---|
| `NUM_CHIP_SEL` | int | 1..8 | TBD | number of independent chip selects (ranks or channels) | B1 |
| `WRLVL_WINDOW_CSR` | CSR | speed-bin | TBD | `tWLMRD`, `tWLDQSEN`, `tWLO`, `tWLOE` windows | B2 |
| `RDLVL_MPR_WINDOW_CSR` | CSR | speed-bin | TBD | MPR readout and pre/post-pattern intervals | B3 |
| `CA_TRAIN_WINDOW_CSR` | CSR | JESD209-4 | TBD | CA training and WDQ calibration intervals | B4 |
| `TRAIN_TIMEOUT_CSR` | CSR | controller-defined | TBD | per-interface timeout, distinct status bit | B5 |

: Table 2.9.1: Training-interface parameters

The JEDEC timing values behind these CSRs are runtime CSRs, initialised from
the JESD79-4 or JESD209-4 speed bin at CSR-derivation time (HAS Ch 5; numeric
constants are HAS open question Q1).

## Interface

### DFI training signal groups

| Signal | Direction | Width | Description |
|---|---|---|---|
| `dfi_phylvl_req_cs_n` | in | `NUM_CHIP_SEL` | PHY requests training per chip select, DFI v4.0 `§TBC(TASK-005)` |
| `dfi_phylvl_ack_cs_n` | out | `NUM_CHIP_SEL` | controller acknowledges training request, DFI v4.0 `§TBC(TASK-005)` |
| `dfi_phy_wrlvl_cs_n` | out | `NUM_CHIP_SEL` | write-leveling chip-select, DFI v4.0 `§TBC(TASK-005)` |
| `dfi_phy_rdlvl_cs_n` | out | `NUM_CHIP_SEL` | read-leveling chip-select, DFI v4.0 `§TBC(TASK-005)` |
| `dfi_phy_calvl_cs_n` | out | `NUM_CHIP_SEL` | CA-training chip-select, DFI v4.0 `§TBC(TASK-005)` |
| `dfi_lvl_pattern` | out | pattern width | training pattern driven during handshake, DFI v4.0 `§TBC(TASK-005)` |
| `dfi_lvl_periodic` | out | 1 | periodic leveling enable, DFI v4.0 `§TBC(TASK-005)` |
| `dfi_ca_capture` | in | capture width | CA training sample from PHY, DFI v4.0 `§TBC(TASK-005)` |

: Table 2.9.2: DFI 4.0 training signals

### CSR / host side

| Signal | Direction | Width | Description |
|---|---|---|---|
| `wrlvl_enable` | in | 1 | start write leveling |
| `rdlvl_enable` | in | 1 | start read leveling |
| `ca_train_enable` | in | 1 | start CA/WDQ training |
| `wrlvl_window` | in | CSR width | `tWLMRD`, `tWLDQSEN`, `tWLO`, `tWLOE` values |
| `rdlvl_window` | in | CSR width | MPR interval values |
| `ca_train_window` | in | CSR width | CA/WDQ interval values |
| `timeout_csr` | in | CSR width | per-interface timeout limit |
| `wrlvl_status` | out | 2-bit | write-leveling telemetry state |
| `rdlvl_status` | out | 2-bit | read-leveling telemetry state |
| `ca_train_status` | out | 2-bit | CA-training telemetry state |
| `wrlvl_result` | out | per-CS | captured prime-DQ value per chip select |
| `rdlvl_result` | out | per-CS | captured MPR pattern per chip select |
| `ca_train_result` | out | per-channel | captured CA/DQ observation |
| `attempt_count` | out | per-interface | how many times this interface was enabled |
| `result_count` | out | per-interface | how many captures completed |
| `timeout_count` | out | per-interface | how many times the timeout CSR expired |

: Table 2.9.3: Host/CSR training interface

## Microarchitecture internals

### `wrlvl_ifc`: write leveling, MODIFIED

The contract is inherited from scoria unchanged. scoria's HAS Ch 3.3 / its
book owns the original contract: DFI leveling handshake, MR1 path in and out
of write-leveling mode, the `tWLMRD`, `tWLDQSEN`, `tWLO`, and `tWLOE` windows
as runtime CSRs, prime-DQ result capture, and the four-state telemetry. The
marking is MODIFIED only because the shared training machinery — handshake
discipline, window enforcement, and telemetry framing — is factored so all
three interfaces ride it. What `wrlvl_ifc` owes the host is exactly what it
owed before.

### `rdlvl_ifc`: MPR read leveling, NEW

DDR4's fly-by topology skews DQS against CK on the read side too. MR3's MPR
(multi-purpose register) makes the DRAM drive a known training pattern onto
DQ, so the controller can observe its read capture timing without the memory
array in the loop. The sequence is:

```text
MRW(MR3, MPR enable + pattern select)
  -> [DFI read-leveling handshake per DFI v4.0]
  -> drive MPR pattern
  -> host reads captured values
  -> MRW(MPR disable)
```

The DFI read-leveling handshake uses `dfi_phylvl_req_cs_n`,
`dfi_phylvl_ack_cs_n`, and `dfi_phy_rdlvl_cs_n`, with `dfi_lvl_pattern`
carrying the training pattern, per DFI v4.0 `§TBC(TASK-005)`. The MPR readout
interval and its pre/post-pattern windows are runtime CSRs, named per
JESD79-4, initialised from the speed bin at CSR-derivation time (HAS Ch 5;
numeric constants are HAS open question Q1). Result capture is per chip select.

### `ca_train_ifc`: LPDDR4 CA/WDQ training, NEW

LPDDR4's CA bus needs training DDR4 doesn't: LPDDR4 samples CA against CK, and
both edges matter. The write-DQ path also needs its own calibration step.
JESD209-4 carries both through MPC training opcodes, which is why this block
sits beside `zq_ctrl`'s MPC submodule and reuses the formatter's LPDDR4 CA
path. The two flows are:

```text
enter CA training (MPC)
  -> sample CA against CK
  -> host reads sample
  -> adjust
  -> exit CA training (MPC)
```

and

```text
enter WDQ calibration (MPC)
  -> drive/training pattern on WDQ
  -> host reads captured value
  -> adjust
  -> exit WDQ calibration (MPC)
```

State is per channel because LPDDR4's two x16 channels train independently.
The training intervals are runtime CSRs, initialised from the JESD209-4 speed
bin at CSR-derivation time (HAS Ch 5; numeric constants are HAS open question
Q1). Whether CA training is mandatory before operation is board-dependent; the
init chapter records it as a conditional step, but the interface exists either
way.

### Four-state telemetry

Every interface reports the same 2-bit status, plus three counters:

```text
status encoding:
  2'b00 = never attempted
  2'b01 = converged
  2'b10 = timed out
  2'b11 = no result in window

counters (per interface):
  attempts  : how many times enable was asserted
  results   : how many times a valid capture completed
  timeouts  : how many times the timeout CSR expired before convergence
```

A detector that has never fired is not evidence of anything. The "never
attempted" state exists so firmware can tell the difference between "I
haven't tried" and "I tried and failed".

## FSM policy

Each interface keeps a minimal handshake FSM. For `rdlvl_ifc` the states are:

```text
IDLE -> MPR_ENTRY -> HANDSHAKE -> CAPTURE -> MPR_EXIT -> REPORT -> IDLE
```

- `IDLE`: waiting for `rdlvl_enable`.
- `MPR_ENTRY`: issue `MRW(MR3, MPR enable + pattern select)` and wait the MPR
  entry interval.
- `HANDSHAKE`: drive `dfi_phylvl_ack_cs_n` and `dfi_phy_rdlvl_cs_n` until the
  PHY acknowledges, per DFI v4.0 `§TBC(TASK-005)`.
- `CAPTURE`: latch the observed MPR pattern per chip select.
- `MPR_EXIT`: issue `MRW(MR3, MPR disable)` and wait the MPR exit interval.
- `REPORT`: update the four-state telemetry and counters, then return to
  `IDLE`.

There are no search states. The host walks the delay line by asserting enable
again with a new delay setting. The same shape applies to `wrlvl_ifc` and
`ca_train_ifc`, with the command path switched from MR3 to MR1 and from MPR to
MPC respectively.

## Timing

- `tWLMRD`: runtime CSR, MR1-write to DQS assertion for write leveling.
- `tWLDQSEN`: runtime CSR, DQS enable window for write leveling.
- `tWLO`: runtime CSR, DQS-to-ODT window observed during write leveling.
- `tWLOE`: runtime CSR, DQS enable-to-DQ window observed during write leveling.
- MPR readout interval: runtime CSR, MR3 entry to valid training pattern.
- MPR pre/post-pattern intervals: runtime CSRs, margins around the MPR drive.
- CA/WDQ training intervals: runtime CSRs per JESD209-4.
- `tMOD`: runtime CSR, wait after any MRW before the next valid command; used
  at MPR entry/exit and at write-leveling MR1 entry/exit.
- All numeric values are runtime CSRs, initialised from the JESD79-4 or
  JESD209-4 speed bin at CSR-derivation time (HAS Ch 5; numeric constants are
  HAS open question Q1).

## Notes

- `wrlvl_ifc` is MODIFIED only by factoring; its visible contract is the same
  as scoria's.
- `rdlvl_ifc` never decides a delay. It only exposes the MPR pattern so
  firmware can decide.
- `ca_train_ifc` is LPDDR4-only in practice, but the structure is generic;
  the MPC issuer is reused with `zq_ctrl`.
- The training blocks touch three neighbors: `init_sequencer` adds
  training-entry states after ZQ, `mode_register` carries MR3 MPR fields and
  LPDDR4 training MRs, and `dfi_cmd_formatter`'s LPDDR4 CA submodule issues
  the MPC opcodes. No datapath block changes for training.
