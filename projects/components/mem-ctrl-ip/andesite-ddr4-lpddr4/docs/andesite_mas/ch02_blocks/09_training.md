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

**Module:** `andesite_wrlvl_ifc` (MODIFIED, carried and landed), `andesite_rdlvl_ifc` (NEW, landed), `andesite_ca_train_ifc` (NEW, landed)
**Location:** `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/fub/`
**Category:** training control / PHY handshake
**Parent:** `andesite_training_layer` / `andesite_top`
**Status:** all three landed; the tables below name the landed port lists

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
| `NUM_CS` | int | 1..8 | 1 | number of independent chip selects (ranks or channels) | B1 |
| `CSW` | int | — | `$clog2(NUM_CS)` (min 1) | chip-select index width (`cs_sel_i`) | B1 |

: Table 2.9.1: Training-interface parameters

The JEDEC timing windows arrive as runtime-CSR ports on the landed `wrlvl_ifc` — `t_wldqsen_i`, `t_wlmrd_i`, `t_wlo_i`, `t_wloe_i` (write leveling, B2) — initialised from the JESD79-4 or JESD209-4 speed bin at CSR-derivation time (HAS Ch 5; numeric constants are HAS open question Q1). The per-interface timeout is `t_wlmrd_max_i` (B5). The rdlvl/CA-training windows (B3, B4) land with those interfaces.

## Interface

### DFI training signal groups

| Signal | Direction | Width | Description |
|---|---|---|---|
| `dfi_phylvl_req_cs_n_o` | out | `NUM_CS` | controller requests per-CS write leveling (DFI leveling handshake, active-low per CS) |
| `dfi_phylvl_ack_cs_n_i` | in | `NUM_CS` | PHY acknowledges the training request per CS |
| `dfi_phy_wrlvl_cs_n_o` | out | `NUM_CS` | write-leveling chip-select to the PHY |
| `dfi_wrlvl_strobe_o` | out | 1 | DQS strobe the PHY forwards for the prime-DQ sample |
| `dfi_phy_rdlvl_cs_n_o` | out | `NUM_CS` | read-leveling chip-select, driven in `rdlvl_ifc`'s HANDSHAKE |
| `dfi_phylvl_req_cs_n_i` | in | `NUM_CS` | PHY read-leveling request per CS (`rdlvl_ifc` handshake input) |

The controller initiates the handshake — the host owns the delay sweep (design decision D2), so there is no PHY-driven request pin on `wrlvl_ifc`; `rdlvl_ifc` consumes the PHY's request and raises its own ack (`dfi_phylvl_ack_cs_n_o` is shared by both interfaces' handshakes on the DFI bus, one training kind at a time).

: Table 2.9.2: DFI 4.0 training signals

### CSR / host side

| Signal | Direction | Width | Description |
|---|---|---|---|
| `wrlvl_en_i` | in | 1 | enter write-leveling mode (the MR1[7] path) |
| `strobe_i` | in | 1 | host strobe — one DQS edge per pulse; the host owns the delay sweep |
| `cs_sel_i` | in | `CSW` | chip select under training |
| `t_wldqsen_i` | in | 16 | `tWLDQSEN` window |
| `t_wlmrd_i` | in | 16 | `tWLMRD` window |
| `t_wlmrd_max_i` | in | 16 | `tWLMRD` timeout (0 = no timeout — the distinct timeout status) |
| `t_wlo_i` | in | 16 | `tWLO` window |
| `t_wloe_i` | in | 16 | `tWLOE` window |
| `prime_dq_i` | in | 1 | sampled prime DQ returned by the PHY |
| `result_valid_o` | out | 1 | a sample completed |
| `result_o` | out | 1 | captured prime-DQ value |
| `obs_attempts_o` | out | 16 | enable/strobe count — how many times the interface ran |
| `obs_flips_o` | out | 16 | result-bit transitions observed across the sweep |
| `obs_timeout_o` | out | 1 | `t_wlmrd_max_i` expired (distinct status) |
| `obs_ever_done_o` | out | 1 | converged at least once |
| `obs_state_o` | out | 3 | FSM-state observability |
| `rdlvl_en_i` | in | 1 | start one read-leveling sweep (a delay setting) |
| `csr_mr3_mpr_enter_i` | in | 16 | MR3 image with MPR enable + pattern select (the RTL makes no MPR-bit-position claim — HAS Q1); `csr_mr3_mpr_exit_i` is the disable image |
| `t_mpr_enter_i` | in | 16 | MRW ack to valid training pattern; `t_mpr_exit_i` / `t_mpr_readout_i` are the exit and capture windows |
| `t_rdlvl_timeout_i` | in | 16 | read-leveling handshake bound (0 = none) |
| `mpr_pattern_i` | in | 1 | observed DQ, latched per chip select in CAPTURE |
| `cmd_req_o` | out | 1 | MRW/MPC request path (shared shape with the init sequencer) |
| `cmd_ack_i` | in | 1 | formatter/scheduler grant for the request |
| `cmd_op_o` | out | 5 | `OP_MRS` (`rdlvl_ifc`) / `OP_MPC` (`ca_train_ifc`) |
| `cmd_bank_o` | out | 3 | MR index (3 = MR3 on the `rdlvl_ifc` MRW path) |
| `cmd_addr_o` | out | 16 | the MR3 image on the MRW path |
| `ca_train_en_i` | in | 1 | start one CA-training round; `wdq_cal_en_i` starts one WDQ-calibration round |
| `csr_mpc_ca_enter_i` | in | 6 | MPC opcode image for CA-training entry (CSR; encodings TBC(JESD209-4) — driven, never decoded); `csr_mpc_ca_exit_i`, `csr_mpc_wdq_enter_i`, `csr_mpc_wdq_exit_i` are the sibling images |
| `t_ca_train_i` | in | 16 | CA sample window; `t_wdq_cal_i` is the WDQ window; `t_ca_timeout_i` bounds the MPC handshake |
| `ca_sample_i` | in | 1 | CA observation during SAMPLE; `wdq_sample_i` is the WDQ observation |
| `mpc_op_o` | out | 6 | the opcode image presented on the MPC issue path |
| `chan_sel_i` | in | 1 | LPDDR4 x16 channel select (channels train independently) |

The telemetry discipline is the landed `wrlvl_*`/`obs_*` shape above, one counter set per interface.

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
- The three FUBs instantiate in `andesite_training_layer`, which owns the DFI
  training pins, the one-active mux, and the maintenance-class command channel
  (`trn_cmd_*`) into the scheduler. `init_sequencer` adds training-entry states
  after ZQ, `mode_register` carries MR3 MPR fields and LPDDR4 training MRs, and
  `dfi_cmd_formatter`'s LPDDR4 CA submodule issues the MPC opcodes. No datapath
  block changes for training.
