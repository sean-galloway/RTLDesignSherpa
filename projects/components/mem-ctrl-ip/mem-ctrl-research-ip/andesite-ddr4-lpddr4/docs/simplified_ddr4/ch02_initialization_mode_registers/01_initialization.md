# Power-Up and Initialization

DDR4 must be brought up through a fixed initialization flow. The mode registers have no reliable power-up defaults, so every defined register must be written before normal traffic is issued. The flow below covers cold power-up and a reset while power remains stable.

## Cold start sequence

1. Apply power with RESET# below 0.2 x VDD and the TEN input also below 0.2 x VDD. Other input levels may be undefined during this phase. RESET# must stay low for at least 200 us once the supplies are stable; TEN must stay low for at least 700 us. CKE must be driven low at least 10 ns before RESET# rises.
2. Keep the voltage ramp within the required windows: VDD and VDDQ are nominally 1.2 V, VPP is nominally 2.5 V; VPP must ramp at the same time or earlier than VDD and must be equal to or higher than VDD at all times; VDD must be greater than or equal to VDDQ and their difference must stay below 0.3 V; the ramp from 300 mV to VDDmin must take no more than 200 ms.
3. Release RESET#, then wait 500 us before raising CKE. During this window the DRAM performs internal state initialization without needing a clock.
4. Start CK/CK# and let it stabilize for at least 10 ns or 5 tCK, whichever is longer, before CKE goes high. A Deselect command must be registered before the CKE rising edge. CKE must stay high without interruption for the rest of initialization, through tDLLK and tZQinit.
5. Keep ODT high-impedance from power-up until CKE is high. If RTT_NOM will be enabled in MR1, hold the ODT pin low from tIS before CKE rises until the end of initialization; otherwise it may be tied low or high but must not toggle.
6. After CKE is registered high, wait tXPR = max(tXS, 5 x tCK) before the first MRS command.
7. Issue MRS commands in this order: MR3, MR6, MR5, MR4, MR2, MR1, MR0. MR0 must include the DLL reset bit (A8 = 1).
8. Issue ZQCL to begin ZQ calibration.
9. Wait until both tDLLK and tZQinit have expired; the device is then ready for read/write training, which includes VrefDQ training and write leveling.

The gaps between commands look like this:

```
... CKE high ... MRS(MR3) ... MRS(MR6) ... MRS(MR5) ... MRS(MR4) ... MRS(MR2) ... MRS(MR1) ... MRS(MR0) ... ZQCL ... ready
        |tXPR| tMRD |  tMRD  |  tMRD  |  tMRD  |  tMRD  |  tMRD  |  tMOD  |     tZQinit     |

Deselect commands must fill every gap from the first MRS through ZQCL.
```

Key timing values:

| Symbol | Value | Meaning |
| --- | --- | --- |
| tMRD | 8 nCK | Minimum gap between consecutive MRS commands |
| tMOD | max(24 nCK, 15 ns) | Minimum gap from an MRS command to a non-MRS command |
| tDLLK | 597 / 768 / 1024 nCK | DLL lock time; value scales with data rate and is programmed in MR6 |
| tZQinit | spec-defined | Long ZQ calibration interval after reset |

## Reset with stable power

If power is already stable and only a reset is required, the sequence is shorter:

1. Drive RESET# below 0.2 x VDD for at least tPW_RESET (1 us). CKE must be low at least 10 ns before RESET# rises.
2. Continue from cold-start step 3: the 500 us wait, clock stabilization, CKE high, and the MRS/ZQCL sequence.
3. After tDLLK and tZQinit expire, the device is ready for training.

## Optional features during initialization

- Gear-down mode (MR3 A3): the DRAM powers up in 1N (1/2 rate) mode. To use 2N (1/4 rate) mode, issue a low-frequency MRS to set MR3 A3 = 1, send a 1N sync pulse, then wait tSYNC_GEAR and tCMD_GEAR before continuing the normal initialization sequence in 2N mode. CAL and CA parity must be disabled before the gear-down MRS and may be re-enabled afterward.
- CA parity mode (MR5 A2:A0): when enabled, MRS-to-MRS and MRS-to-command delays become tMRD_PAR = tMOD + PL and tMOD_PAR = tMOD + PL, where PL is the programmed parity latency.
- CAL mode (MR4 A8:A6): when enabled, MRS-to-command delays become tMOD_CAL = tMOD + tCAL and MRS-to-MRS delays become tMRD_CAL = tMOD + tCAL.

## Notes that bite

- The seven mode registers are not initialized to defined values by hardware; they must all be written explicitly. Skipping one leaves undefined settings.
- Every MRS command requires all banks precharged and idle, tRP satisfied, all bursts finished, and CKE high.
- The DLL must be enabled (MR1 A0 = 1) before it is reset (MR0 A8 = 1). After any DLL reset, wait tDLLK before issuing a Read or any synchronous ODT operation.
- ZQ calibration initializes the output driver and ODT impedance; it is required before normal operation, not optional.
- During initialization, ODT is not active even if the eventual MR1 setting will enable RTT_NOM. Do not rely on termination until after tDLLK and tZQinit.
- Some MRS changes are exempt from plain tMRD/tMOD and have their own settling rules; these include gear-down entry, CA parity, CAL, per-DRAM addressability, VrefDQ training, and maximum power saving mode.

**Source:** JESD79-4D sections 3.3, 3.4.1, 4.15, 4.17, 4.18
