# Power-Up and Initialization

LPDDR4 must follow a fixed bring-up sequence; any deviation is undefined. Each channel initializes independently, though a single RESET_n pin resets every channel on the die. This chapter describes one channel; repeat the same steps for the other.

## Cold-start sequence

1. **Voltage ramp (Ta -> Tb).** Apply VDD1, VDD2 and VDDQ while RESET_n is held LOW (<= 0.2 x VDD2) and CKE is LOW. Ta is the first moment any supply reaches 300 mV; Tb is when every supply and reference is inside its operating range. The ramp must finish within tINIT0 = 20 ms. During the ramp: VDD1 must stay at or above VDD2; VDD2 must stay at or above VDDQ - 200 mV; VSS/VSSQ/VSSCA must stay within 100 mV of each other; and DQ/DMI/DQS_t/DQS_c must stay between VSSQ and VDDQ while CKE/CS/CA/CK must stay between VSS and VDD2.
2. **RESET_n hold (Tb -> Tc).** Keep RESET_n LOW for at least tINIT1 = 200 us after Tb. At least 10 ns before releasing RESET_n, drive CKE LOW.
3. **Clock and CKE (Tc -> Td).** After RESET_n rises, wait at least tINIT3 = 2 ms before taking CKE HIGH. The differential clock must be stable for at least tINIT4 = 5 tCK before CKE goes HIGH. CS must be LOW when CKE rises.
4. **Idle wait (Td -> Te).** With CKE HIGH, issue only DES (NOP) for at least tINIT5 = 2 us. The clock must remain inside the boot window tCKb during MRW and MRR commands issued here; some AC parameters such as tDQSCK are relaxed until full configuration.
5. **Configure I/O (Te -> Tf).** Issue MRW commands to set pull-up calibration point (MR3 PU-CAL), pull-down drive strength (MR3 PDDS), DQ ODT (MR11 OP[2:0]) and CA ODT (MR11 OP[6:4]). These values are needed before ZQ calibration latches.
6. **ZQ calibration (Tf -> Th).** Issue the MPC ZQCal Start command. Wait tZQCAL = 1 us, then issue the MPC ZQCal Latch command. Keep the CA bus deselected for tZQLAT = max(30 ns, 8 tCK) so the latched values update the DQ drivers and CA/DQ termination. Do not overlap ZQCal Start commands across devices that share one ZQ resistor.
7. **Command bus training (Th).** Enter command-bus training (MR13 OP[0] = 1) to align CS/CA with CK and set the internal VREF(CA) level. The device powers up with low-speed receiver defaults, so speeds above tCKb require this step.
8. **Write leveling (Ti).** Enable write leveling (MR2 OP[7] = 1) and adjust DQS_t/DQS_c timing so the device recognizes the start of a write burst at the programmed WL. Clear MR2 OP[7] to exit.
9. **DQ bus training (Tj).** Use MPC Read FIFO, Write FIFO and Read DQ Calibration together with MRW updates to MR14 to train VREF(DQ), DQS and DQ timing.
10. **Normal operation (Tk).** The channel is now ready for any valid command. Write any remaining operating mode registers (burst length, RL/WL, DBI, etc.).

```
ramp <=20ms   RESET 200us   RESET_n ->    CKE ->      DES 2us     MRW IO cfg    MPC ZQStart   MPC ZQLatch    CBT      WL      DQ train   ready
|___tINIT0____|__tINIT1_____|__tINIT2_____|__tINIT3___|__tINIT5___|____Te___|____tZQCAL____|___tZQLAT_____|__Th___|__Ti___|____Tj____|__Tk__
                          tINIT2=10ns CKE low before RESET_n high
                          tINIT4=5tCK stable clock before CKE high
```

| Parameter | Min | Max | Unit | Meaning |
| --- | --- | --- | --- | --- |
| tINIT0 | - | 20 | ms | longest allowed supply ramp |
| tINIT1 | 200 | - | us | RESET_n LOW after all supplies valid |
| tINIT2 | 10 | - | ns | CKE LOW before RESET_n rises |
| tINIT3 | 2 | - | ms | CKE LOW after RESET_n rises |
| tINIT4 | 5 | - | tCK | stable clock before CKE rises |
| tINIT5 | 2 | - | us | DES wait after CKE goes HIGH |
| tZQCAL | 1 | - | us | ZQ calibration time |
| tZQLAT | max(30ns, 8tCK) | - | ns | quiet CA bus after ZQCal Latch |
| tCKb | 18 | note | ns | boot clock period; system may start faster |

## Reset with stable power

Drive RESET_n below 0.2 x VDD2 for at least tPW_RESET = 100 ns, with CKE LOW at least 10 ns before RESET_n rises. Then repeat steps 3-10 of the cold-start sequence. Mode registers return to defaults and SDRAM contents become undefined.

## Power-off sequence

Controlled power-off reverses the ramp rules. Hold CKE LOW (<= 0.2 x VDD2) and keep all other inputs between VILmin and VIHmax; outputs remain High-Z. Tx is when any supply first drops below its minimum; Tz is when all supplies are below 300 mV. Between Tx and Tz, VDD1 must stay above VDD2 and VDD2 must stay above VDDQ - 200 mV; VSS pins must stay within 100 mV. The fall from Tx to Tz must not exceed tPOFF = 2 s.

Uncontrolled power-off is tolerated only with tighter limits: at Tx all supplies must turn off and supply current capacity must reach zero except for residual charge; VDD1 and VDD2 must fall with slope <= 0.5 V/us between Tx and Tz; and this may occur at most 400 times over the device's life.

## Notes that bite

- LPDDR4 has no DAI bit; the device is ready for MRW/MRR after tINIT5. Do not poll MR0 for an initialization-done flag.
- Boot-frequency AC relaxations apply until command-bus, write-leveling and DQ-bus training are complete.
- ZQCal Start may be issued to either or both channels of a dual-channel die, but ZQCal Latch is required per channel.
- Deep power-down exit requires the full power-up initialization sequence.

**Source:** JESD209-4E sections 3.3.1, 3.3.2, 3.3.3, 3.3.4
