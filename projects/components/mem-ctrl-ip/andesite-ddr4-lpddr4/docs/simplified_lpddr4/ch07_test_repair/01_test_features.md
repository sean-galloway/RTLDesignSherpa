# Test Features

LPDDR4 has no DDR4-style MPR pages, no device-level boundary scan, no OCD engine, no write CRC, and no gear-down mode. Instead it exposes a rich set of calibration and observation features reached through MRW/MRR and the MPC command. The two channels of a dual-channel die are largely independent, although they share the ZQ pin and calibration circuit.

## VRCG high-current VREF generator

Set MR13 OP3 to 1 to engage the high-current VREF generator. This shortens the settling time of VREF(CA) and VREF(DQ) during training or when switching frequency set points. Only Deselect commands are legal until tVRCG_ENABLE elapses (max 200 ns). Clear MR13 OP3 to leave high-current mode and wait tVRCG_DISABLE (max 100 ns) before normal traffic. Range and value changes can still be done without VRCG, but they take longer.

## CA and DQ VREF training

The CA receiver reference is tied to VDD2 and programmed in MR12, while the DQ receiver reference is tied to VDDQ and programmed in MR14. Because the two buses use different supplies, terminations, and swing environments, their reference levels are trained independently. Each register has a range bit (OP6) and a 6-bit value (OP[5:0]). One step is about 0.4% of the relevant supply. Wait the appropriate VREF step time between MRW updates.

| Change type | Time |
| --- | --- |
| Single step | max 100 ns |
| Two or more steps in the same range | max 200 ns |
| Full range sweep | max 250 ns |
| Without VRCG high-current mode | max 1 ms |

## Command bus training

Enter Command Bus Training by setting MR13 OP0 to 1; after tMRD, drive CKE low. While CKE is low the DRAM uses the alternate FSP register copy; when CKE goes high it returns to the copy that was active before entry. Trained values are not retained, so write them to the FSP-WR registers before returning to the trained frequency.

For x16 devices, DQ[6:0] carries the desired VREF(CA) value, DQ6 selects the range, DQS0 toggles to latch it, and DQ[13:8] echoes the latched CA values. For byte (x8) devices there are two modes: Mode 1 echoes CA on DQ[5:0] and the VREF value is written beforehand via MRW; Mode 2 reuses DQ[5:0] first as VREF inputs and then as CA echoes, controlled by DQ7. In multi-rank systems train the terminating rank first, then turn on its termination while training the non-terminating rank.

Key timings include tCAENT (250 ns), tVREFCA_LONG (250 ns), tVREFCA_SHORT (80 ns for x16, 100 ns for byte Mode 2), tADR (20 ns), tXCBT (200 ns or 250 ns), and tMRZ (1.5 ns).

## Frequency Set Points

Two complete copies of MR1, MR2, MR3, MR11, MR12, MR14, and MR22 are selected by MR13 OP6 (FSP-WR, which copy is read or written) and MR13 OP7 (FSP-OP, which copy is active). This lets the controller set up a new frequency, voltage swing, and termination point in the background, then switch atomically. To change FSP-OP, set MR13 OP7 and engage VRCG high-current at the same time, then wait tFC before resuming normal commands. tFC is 200 ns for a single VREF step or same-range changes and 250 ns when the VREF range changes. The device boots from FSP-OP[0] with un-terminated, low-frequency defaults.

## Write leveling

Set MR2 OP7 to 1 to enter write-leveling mode. The DRAM samples CK on each rising DQS edge and asynchronously returns the sampled value on every DQ bit of that byte after tWLO. The controller adjusts the DQS delay until it sees a 0-to-1 transition. Both byte strobes in a channel are leveled independently, and dual-channel parts train each channel separately. Write leveling should be completed before DQS-DQ write training.

| Symbol | Meaning | Value |
| --- | --- | --- |
| tWLDQSEN | DQS quiet after mode entry | min 20 tCK |
| tWLMRD | First DQS edge after mode entry | min 20 tCK |
| tWLO | Feedback output delay | 0 to 20 ns |
| tMRD | Exit MRW to valid command | min max(14 ns, 10 tCK) |
| tWLS/tWLH | DQS setup/hold to CK | speed-grade dependent |

## RD DQ calibration and read preamble training

Issue MPC-1 [RD DQ Calibration] followed immediately by CAS-2. The DRAM drives the MR32 pattern then the MR40 pattern on every DQ and DMI pin, using normal read-latency timing. MR15 and MR20 provide per-byte invert masks. Default values are MR32=5Ah, MR40=3Ch, and both masks=55h.

Read preamble training, enabled by MR13 OP1=1, holds DQS_t low and DQS_c high until the next RD DQ Calibration. This quiet strobe is useful for training the DQS receivers. Both features are optional; check the vendor data sheet.

## DQS-DQ training

Because the internal DQS and DQ paths are not matched, the controller delays DQ relative to DQS to center the data eye. Training uses MPC [Write DQ FIFO] and [Read DQ FIFO], each followed immediately by CAS-2 and using normal write/read latencies. Up to five BL16 bursts can be written into the FIFO, then read back and compared against expected data.

The FIFO pointers reset at power-up, RESET_n assertion, power-down entry, or self-refresh power-down entry. To keep read and write pointers aligned, the number of Read FIFO commands must equal the number of Write FIFO commands modulo the FIFO depth of five.

## DQS interval oscillator

A built-in ring oscillator copies the DQS clock tree to track delay drift caused by voltage and temperature changes. Start it with MPC [Start DQS Osc] and stop it with MPC [Stop DQS Osc] or an MR23 automatic-stop count; the result is stored in MR18 (LSB) and MR19 (MSB). Longer run times reduce granularity error, which is roughly 2 * tDQS2DQ / runtime. The count tells the controller whether retraining is needed and how large the timing error might be.

## Multi-purpose command

MPC is a single opcode vehicle for training and calibration. OP6=0 is a NOP; OP6=1 selects a training function. Read/write functions (Write FIFO, Read FIFO, RD DQ Calibration) must be followed immediately by CAS-2 with operands driven low. Other MPC functions are Start/Stop DQS Oscillator, ZQCal Start, and ZQCal Latch.

## Thermal offset and temperature sensor

MR4[6:5] applies a controller-supplied thermal offset to the channel's temperature-compensated self-refresh circuit; it can take up to 200 us to appear in MR4[2:0]. The on-die temperature sensor reports status through MR4 and updates at most every tTSI=32 ms. To avoid missing thermal events, the host polling interval must satisfy TempGradient * (ReadInterval + tTSI + SysRespDelay) <= 2C.

## ZQ calibration

ZQ calibration is started with MPC [ZQCal Start] and captured with MPC [ZQCal Latch]. Allow tZQCAL=1 us before latching and keep CA deselected during tZQLAT. A ZQCal Reset via MR10 OP0 returns drivers to +/-30% accuracy in tZQRESET. Dual-channel devices share one ZQ pin and calibration circuit, but each channel latches its own values. The ZQ ball needs a 240 ohm +/-1% resistor to VDDQ and no more than 25 pF of loading.

## Refresh management

Devices that need extra refresh under heavy traffic set MR24 OP0=1. The controller counts ACT commands per bank (RAA). When RAA reaches the vendor threshold RAAIMT in MR24[5:1], issue RFMab or RFMpb to give the DRAM extra refresh-management time. RFM decrements RAA by RAAIMT * RAADEC from MR36[1:0]; REF commands also decrement by RAAIMT. RAA must never exceed RAAMMT = RAAIMT * RAAMULT from MR24[7:6]; if it does, no further ACTs to that bank are legal until REF or RFM lowers it. Representative tRFMab/tRFMpb values are 210/170 ns for 8 Gb and 280/190 ns for 12/16 Gb.

## Post-package repair

PPR is optional and repairs one fail row per bank per die by blowing an electrical fuse; status is readable in MR25. Procedure: precharge all banks; set MR4 OP4=1 and wait tMRD; ACT to the failing row; wait tPGM=1 s; PRE; wait tPGM_Exit=15 ns; clear MR4 OP4; wait tPGMPST=50 us; issue RESET and reinitialize. Only one row per bank can be repaired and the fuse cannot be undone. Memory contents are not refreshed during PPR and may be lost.

## What is not here

- No MPR page concept; read training uses MRR and MPC-based RD DQ Calibration.
- No device-level boundary scan, no OCD calibration engine, no write CRC, no gear-down mode, and no per-pin loopback.

**Source:** JESD209-4E sections 4.25-4.38, 4.47, 4.48
