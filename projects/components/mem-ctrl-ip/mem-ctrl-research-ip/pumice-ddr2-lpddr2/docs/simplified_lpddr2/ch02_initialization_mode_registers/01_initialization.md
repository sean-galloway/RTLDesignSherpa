# Power-Up and Initialization

LPDDR2 must be powered up and initialized by a fixed sequence; any other
procedure is undefined behavior. The sequence below paraphrases the
mandatory steps. Named checkpoints (Ta..Tg) are the spec's.

## Cold start sequence

1. **Power ramp (Ta -> Tb).** Apply supplies with CKE held low
   (<= 0.2 x VDDCA). Ta is when any supply first reaches 300 mV; Tb is
   when all supplies and references are in range. The ramp (tINIT0) must
   complete within 20 ms. Ordering rules during the ramp: VDD1 within
   200 mV above VDD2, VDD1/VDD2 within 200 mV above VDDCA and VDDQ, VREF
   always below every supply, ground pins within 100 mV of each other.
2. **CKE and clock (Tb -> Tc).** Keep CKE low for at least
   tINIT1 = 100 ns after Tb. The clock must be stable for at least
   tINIT2 = 5 tCK before CKE's first low-to-high transition. If any
   mode-register reads will be done during init, the clock must be in
   the boot range tCKb = 18-100 ns (about 10-55 MHz).
3. **NOP wait (Tc -> Td).** With CKE high, issue NOP for at least
   tINIT3 = 200 us.
4. **Reset (Td).** Issue MRW Reset (an MRW to MR63; any operand). Then
   hold CKE high with NOPs for at least tINIT4 = 1 us.
5. **DAI polling (Td -> Tf).** Only MRR and power-down entry/exit are
   legal now. Poll MR0's DAI bit (or simply wait tINIT5 = 10 us for
   SDRAM) until the device reports auto-initialization complete; the
   device is then Idle. This is also when MRRs of MR0/MR5/MR8 identify
   device type, manufacturer, density and IO width.
6. **ZQ calibration (Tf -> Tg).** Issue MRW ZQ Initialization
   Calibration (MR10, code 0xFF). The device is ready for normal
   operation after tZQINIT (1 us). On multi-device buses, ZQ
   calibrations must not overlap.
7. **Configure.** MRW the operating registers: MR1 (burst length, burst
   type, wrap, nWR), MR2 (RL/WL), MR3 (drive strength). The device is
   now Idle and accepts any valid command.

```
ramp <=20ms  CKE __/  NOP 200us  MRW63  NOP 1us  MRR0(DAI)  MRW10(0xFF)  MRW1,2,3
|__tINIT0____|_tINIT1_|_tINIT3_|      |_tINIT4_|__tINIT5____|__tZQINIT___|  ready
              tINIT2 = 5 tCK of stable clock before CKE rises
```

## Reset without power ramp

An MRW Reset issued later (outside power-up) restarts initialization at
step 4: reset the mode registers to defaults, wait tINIT4, poll DAI or
wait tINIT5, redo ZQ calibration and the MRW configuration. SDRAM array
contents are undefined after MRW Reset.

## Power-off

Controlled power-off mirrors the ramp rules in reverse: hold CKE low
while supplies fall, keep all inputs between their rails to avoid
latch-up, and complete the fall (Tx -> Tz, all supplies below 300 mV)
within tPOFF = 2 s. The same supply-ordering inequalities apply during
the fall.

Uncontrolled power-off is tolerated only within tightened bounds the
spec gives separately; the safe design rule is that a system that cannot
guarantee the controlled sequence must treat DRAM contents as lost.

## Notes that bite

- Mode-register contents have defaults only after Device
  Auto-Initialization; before the MRW Reset they are undefined.
- MR1, MR2 and MR3 must all be written even if the defaults look right -
  the whole flow assumes it.
- Boot-frequency rules (tCKb, tISb, tIHb, tDQSCKb) apply until the
  device is configured; some AC parameters are relaxed before then.
- After DPD exit, the full power-up sequence from step 3 applies.

**Source:** JESD209-2F sections 3.4.1-3.4.4, 5.13.3
