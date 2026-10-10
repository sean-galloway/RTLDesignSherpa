# PHY Calibration CSR Contract — mc_training_layer ↔ PHY mechanism boundary

**Status:** v1.0 as-built (Phase 2, Task 4, 2026-10-10)
**Authority:** spec §3.4 — common owns the training CONTROL PLANE; the delay
tap / bitslip / phase MECHANISM stays PHY-vendor-specific behind this
documented contract. A PHY satisfies the contract by implementing the CSR
surface below (or a documented superset); the training layer and all board
firmware speak only this contract.

## Why a contract

The training layer sequences JEDEC training flows (write leveling, DQ
calibration, read alignment, CA training hand-off) and aggregates telemetry.
The mechanisms it drives — per-bit delay lines, bitslip, DQS phase, command
delay — are FPGA-vendor primitives (Xilinx IDELAY/ODELAY/bitslip today;
UniPHY-style delay chains or custom PHYs tomorrow). Without this contract
the control plane drifts into vendor coupling one `(* ASYNC_REG *)` at a
time. The contract pins the BEHAVIOR, not the silicon.

## Contract surface

One 32-bit CSR slave per PHY instance (address width ≤ 10 bits), written by
training firmware through the harness CSR passthrough. Registers are grouped
by mechanism; every counter/register follows the same reset/increment
discipline.

### Write leveling

| Reg | Acc | Semantics |
|---|---|---|
| `WLEVEL_EN` | RW | 1 = DQS-driven leveling mode active (MR1 WL entry assumed done by the control plane) |
| `WLEVEL_STROBE` | RW1S | Write 1 to capture one leveling sample; self-clears |
| `WLEVEL_RESULT` | RO | Last sampled DQ value (the bit the DQ-cal pattern expects) |

### Read path delay (per DQ bit)

| Reg | Acc | Semantics |
|---|---|---|
| `RDLY_DQ_RST` | WO | Reset all selected read DQ delay taps to 0 |
| `RDLY_DQ_INC` | WO | Increment selected bits' read DQ tap by 1 (monotonic, saturating at tap max) |
| `RDLY_DQ_BITSLIP_RST` | WO | Clear read bitslip state |
| `RDLY_DQ_BITSLIP_INC` | WO | Advance read bitslip one step (modulo the ISERDES/bit order) |

### Write path delay (per DQ bit and per DQS)

| Reg | Acc | Semantics |
|---|---|---|
| `WDLY_DQ_RST` / `WDLY_DQ_INC` | WO | As read path, write DQ taps |
| `WDLY_DQS_RST` / `WDLY_DQS_INC` | WO | As read path, DQS taps |
| `WDLY_DQ_BITSLIP_RST` / `WDLY_DQ_BITSLIP_INC` | WO | Write bitslip state |

### Phase / global

| Reg | Acc | Semantics |
|---|---|---|
| `RDPHASE` | RW | DFI read-data phase select (0..DFI_RATE-1) |
| `WRPHASE` | RW | DFI write-data phase select |
| `DLY_SEL` | RW | Bit/group select governing which DQ/DQS the delay strobes touch |
| `HALF_SYS8X_TAPS` | RO | PHY-reported taps per half sys8x cycle (calibration constant) |

### Command/address delay (optional)

| Reg | Acc | Semantics |
|---|---|---|
| `CDLY_RST` / `CDLY_INC` | WO | Command-delay tap (fly-by skew compensation); absence documented per PHY |

## Behavioral requirements (normative)

1. **Reset-then-increment idempotence**: `*_RST` returns the tap/bitslip to
   a known zero state; `*_INC` from zero is deterministic. Firmware may walk
   a window by RST + N×INC without reading back.
2. **Monotonic taps**: `*_INC` never decreases a tap; saturation at the
   device max is legal; wrap is NOT.
3. **Readback**: `RDPHASE`, `WRPHASE`, `DLY_SEL`, `HALF_SYS8X_TAPS`,
   `WLEVEL_RESULT` read back the live state. Delay tap values themselves
   need not be readable (the walk is open-loop by design).
4. **Strobe self-clear**: `*_STROBE` / `*_INC` / `*_RST` write-1 pulses
   self-clear; polling them must return 0.
5. **Clock-domain honesty**: the PHY documents which clock domain each CSR
   lives in; firmware sequences writes across the `ctl_clk`/`dfi_clk`
   boundary via the harness's existing CDC discipline.

## Reference implementation: the generated K7 PHY (k7ddrphy)

`projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/build-scoria/rtl/generated/k7ddrphy.v`
implements this contract with `wlevel_en/strobe`, `rdly_dq_*`,
`rdly_dq_bitslip_*`, `wdly_*`, `rdphase/wrphase`, `dly_sel`,
`half_sys8x_taps`, `cdly_*` — the exact register names the board firmware
(`host/scoria_char.py` et al.) already drive. That firmware is the contract's
first client and its conformance test.

## Known non-covered mechanisms (recorded, not silently dropped)

- **LPDDR4 CA training** (andesite's `ca_train_ifc`): the MPC/MR41-based CA
  bus training is LPDDR4-specific and lives in the andesite rock today. When
  a second customer appears it either joins this contract as a CA-training
  group or graduates into its own document. Tracked in the andesite lane.
- **VREF training** (DDR4): no current rock exercises it; the contract
  reserves the `CDLY` group address range for a future `VREF_*` family.
