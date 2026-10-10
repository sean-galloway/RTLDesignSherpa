# Power-Up and Initialization

LPDDR3 must be brought up with a fixed sequence; any other path is undefined. Reset is command-based only - the spec has no dedicated SDRAM RESET# pin (the RST_n ball in PoP ballouts is an eMMC signal), so the reset event is an MRW to MR63.

## Cold-start sequence

1. **Power ramp (Ta -> Tb).** Apply supplies while CKE is held LOW (<= 0.2 x VDDCA). Ta is when any supply first reaches 300 mV; Tb is when every supply and VREF is inside its operating range. The ramp (tINIT0) must finish within 20 ms. During the ramp: VDD1 must stay within 200 mV above VDD2; VDD1 and VDD2 must stay within 200 mV above VDDCA and VDDQ; VREF must be below every supply; and VSS/VSSQ/VSSCA must be within 100 mV of each other. DQ, DM, DQS_t and DQS_c must stay between VSSQ and VDDQ; CK_t, CK_c, CS_n and CA must stay between VSSCA and VDDCA, to avoid latch-up. Device outputs are High-Z while CKE is LOW.
2. **Clock and CKE (Tb -> Tc).** Keep CKE LOW for at least tINIT1 = 100 ns after Tb. The clock must be stable for at least tINIT2 = 5 tCK before CKE's first LOW-to-HIGH transition. If any MRR will be issued during init, the clock period must be inside the boot window tCKb = 18-100 ns. CKE, CS_n and CA must meet setup/hold from the first rising edge onward. The ODT input may be undefined until tIS before CKE is registered HIGH, then must be held static LOW or HIGH until initialization is complete (including tZQINIT).
3. **NOP wait (Tc -> Td).** With CKE HIGH, issue NOP for at least tINIT3 = 200 us.
4. **MRW RESET (Td).** Issue an MRW RESET (MR63). An optional PRECHARGE ALL may precede it. Keep CKE HIGH with NOPs for at least tINIT4 = 1 us; only NOPs are allowed during this time.
5. **DAI polling (Te -> Tf).** Only MRR and power-down entry/exit are legal now. Poll MR0's DAI bit, or simply wait tINIT5(max) = 10 us. The device is idle once DAI indicates completion or when tINIT5(max) expires. This is also the normal point to read MR8 (and MR5-MR7) to discover I/O width, density, manufacturer and revision.
6. **ZQ calibration / CA training (Tf -> Tg).** If CA training is required, start it at Tf using MR41 (or MR48 for the second mapping) and exit with MR42; no CA commands other than RESET or NOP may be issued until training finishes (Tf'). Then issue the MRW ZQ initialization calibration command (MR10, code 0xFF). If CA training is not needed, ZQ initialization may start at Tf directly. On a shared ZQ bus, do not overlap ZQ calibrations across devices. The device is ready for normal operation after tZQINIT = 1 us.
7. **Configure (after Tg).** MRW the operating registers: MR1 (burst length, nWR), MR2 (RL/WL, write-leveling enable, WL set), MR3 (drive strength) and MR11 (DQ ODT). The device is now idle and accepts any valid command.

```
ramp <=20ms  CKE __/  NOP 200us  MRW63  NOP 1us  MRR0(DAI)  [CA train]  MRW10(0xFF)  MRW1,2,3,11
|__tINIT0____|_tINIT1_|_tINIT3_|      |_tINIT4_|__tINIT5___|__[Tf->Tf']__|__tZQINIT___|  ready
              tINIT2 = 5 tCK of stable clock before CKE rises
```

| Parameter | Min | Max | Unit | Meaning |
| --- | --- | --- | --- | --- |
| tINIT0 | - | 20 | ms | longest allowed supply ramp |
| tINIT1 | 100 | - | ns | CKE must stay LOW after supplies are valid |
| tINIT2 | 5 | - | tCK | stable clock before CKE rises |
| tINIT3 | 200 | - | us | NOP wait after CKE goes HIGH |
| tINIT4 | 1 | - | us | NOP wait after MRW RESET |
| tINIT5 | - | 10 | us | maximum device auto-initialization time |
| tZQINIT | 1 | - | us | ZQ initialization calibration |
| tCKb | 18 | 100 | ns | boot clock period for MRR during init |

## Reset without power ramp

An MRW RESET issued later (with all banks idle) restarts initialization at Td: mode registers return to defaults, wait tINIT4, poll DAI or wait tINIT5, redo ZQ initialization, then reconfigure MR1/MR2/MR3/MR11. SDRAM contents are undefined after MRW RESET.

## Power-off sequence

Controlled power-off is the ramp rules in reverse. Hold CKE LOW (<= 0.2 x VDDCA); keep all other inputs between VILmin and VIHmax; outputs remain High-Z. DQ, DM, DQS_t and DQS_c must remain between VSSQ and VDDQ; CK_t, CK_c, CS_n and CA must remain between VSSCA and VDDCA. Tx is when any supply first drops below its minimum; Tz is when all supplies are below 300 mV. Between Tx and Tz the same supply-order inequalities apply as during ramp, and VSS pins must stay within 100 mV. The fall from Tx to Tz must not exceed tPOFF = 2 s.

Uncontrolled power-off is tolerated only with tighter limits: at Tx all supplies must turn off and supply current capacity must reach zero (except residual charge); VDD1 and VDD2 must fall with slope <= 0.5 V/us between Tx and Tz; and this may occur at most 400 times over the device's life.

## Notes that bite

- Mode-register defaults are valid only after MRW RESET and DAI completion; before that they are undefined.
- MR1, MR2 and MR3 must be written even if the default values look acceptable.
- Boot-frequency AC relaxations (tDQSCKb, etc.) apply until the device is fully configured.
- Deep power-down exit requires the full power-up initialization sequence from step 3.

**Source:** JESD209-3C sections 3.3.1, 3.3.2, 4.11, 4.11.1.1
