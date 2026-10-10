# Power-Up and Initialization

DDR3 must be brought up through a fixed initialization flow; deviating from it produces undefined behavior. The flow below covers both cold power-up and a reset while power remains stable.

## Cold start sequence

1. Apply power with RESET# held below 0.2 x VDD. Other input levels are allowed to be undefined during this phase. RESET# must stay low for at least 200 us once the supplies are stable, and CKE must be driven low at least 10 ns before RESET# rises.
2. Keep the voltage ramp within the required windows: from 300 mV up to VDDmin in no more than 200 ms, with VDD at or above VDDQ and the difference between them under 0.3 V. Either use a single regulator for VDD/VDDQ (with all non-power pins bounded between VSS/VSSQ and VDD/VDDQ, VTT clamped to 0.95 V max after ramp, and VREF following VDDQ/2), or ramp VDD no later than VDDQ and VDDQ no later than VTT and VREF while avoiding slope reversals.
3. Release RESET#, then wait 500 us before raising CKE. During this window the DRAM performs internal state initialization without needing a clock.
4. Start CK/CK# and let it stabilize for at least 10 ns or 5 tCK, whichever is longer, before CKE goes high. A NOP or Deselect command must be registered before the CKE rising edge, and CKE must stay high without interruption for the rest of initialization, through tDLLK and tZQinit.
5. Keep ODT high-impedance from power-up until CKE is high. If RTT_NOM is enabled in MR1, hold the ODT pin low from tIS before CKE rises until the end of initialization; otherwise it may be tied low or high but must not toggle.
6. After CKE is registered high, wait tXPR = max(tXS, 5 x tCK) before the first MRS command.
7. Issue MRS to load MR2 (BA2=0, BA1=1, BA0=0).
8. Issue MRS to load MR3 (BA2=0, BA1=1, BA0=1).
9. Issue MRS to load MR1 with the DLL enabled (A0=0; BA2=0, BA1=0, BA0=1).
10. Issue MRS to load MR0 and reset the DLL (A8=1; BA2=0, BA1=0, BA0=0).
11. Issue ZQCL to begin ZQ calibration.
12. Wait until both tDLLK and tZQinit have expired; then normal operation may begin.

The required gaps look like this:

```
... CKE high ... MRS(MR2) ... MRS(MR3) ... MRS(MR1) ... MRS(MR0) ... ZQCL ... ready
        |tXPR| tMRD | tMRD |    tMRD    |  tMOD  |     tZQinit     |

NOP/Deselect must fill every gap from the first MRS through ZQCL.
```

## Reset with stable power

If power is already stable and only a reset is required, the sequence is shorter:

1. Drive RESET# below 0.2 x VDD for at least 100 ns. CKE must be low at least 10 ns before RESET# rises.
2. Continue from cold-start step 2 (500 us wait, clock stabilization, CKE high, and so on).
3. After tDLLK and tZQinit expire, the device is ready.

## Notes that bite

- The four mode registers are not initialized to defined values by hardware; they must all be written explicitly. Skipping one leaves undefined settings.
- Every MRS command requires all banks precharged and idle, CKE high, tMRD before the next MRS, and tMOD before a non-MRS command such as ZQCL or an ACT.
- The DLL must be enabled (MR1 A0 = 0) before it is reset (MR0 A8 = 1). After any DLL reset, wait tDLLK before issuing a Read or any synchronous ODT operation.
- ZQ calibration initializes the output driver and ODT impedance; it is required before normal operation, not optional.
- During initialization, ODT is not active even if the eventual MR1 setting will enable RTT_NOM. Do not rely on termination until after tDLLK and tZQinit.

**Source:** JESD79-3F sections 3.3.1, 3.3.2
