# Commands: Rules and Constraints

LPDDR3 has no Mode Register Set command; mode-register updates use MRW and reads use MRR. There is no DLL, no additive latency, no burst terminate, and no burst chop. BL8 is the only burst length.

## ACT - Activate

Opens row R in bank B so column accesses can follow.

- Encoding: CS_n low, CA0r low, CA1r high; CA2r-CA3r carry R8-R9, CA4r-CA6r carry R10-R12, and CA7r-CA9r select the bank; the falling edge carries R0-R7 plus R13-R14.
- RD or WR to the same bank may follow after tRCD.
- ACT to a different bank needs tRRD; ACT to the same bank again needs a PRE first and must satisfy tRAS (ACT-to-PRE) and tRC (ACT-to-ACT).
- On 8-bank devices, no more than four ACT or REFpb operations may fall inside a rolling tFAW window.

Key timing:

| Symbol | Rule |
| --- | --- |
| tRRD | max(10 ns, 2 nCK) between ACTs to different banks |
| tFAW | max(50 ns, 8 nCK) rolling window for four bank activations |
| tRAS | min = max(42 ns, 3 nCK); max = min(70.2 us, 9 x RM x tREFI) |
| tRC | tRAS + tRPab (with PREab) or tRAS + tRPpb (with PREpb) |

## RD - Burst read

Starts a fixed BL8 read burst from the open row.

- Encoding: CS_n low, CA0r high, CA1r low, CA2r high; CA5r-CA6r = C1-C2, CA7r-CA9r = bank, and the falling edge carries AP plus C3-C11.
- RL is programmed in the mode registers. Data is valid after RL x tCK + tDQSCK + tDQSQ from the command edge. Because there is no DLL, tDQSCK spans a wide min/max range.
- Back-to-back reads to any bank are spaced by tCCD = 4 clocks.
- A PRE to the same bank may follow after BL/2 + max(4, RU(tRTP/tCK)) - 4 clocks, and tRAS must also be satisfied.
- **tRTW (book symbol):** the earliest WR after a RD is RL + RU(tDQSCKmax/tCK) + BL/2 + 1 - WL clocks after the RD command.

Key timing:

| Symbol | Rule |
| --- | --- |
| tRTP | max(7.5 ns, 4 nCK) analog delay from read to PRE |

## WR - Burst write

Starts a fixed BL8 write burst.

- Encoding: CS_n low, CA0r high, CA1r low, CA2r low; column, bank, and AP mapping matches RD.
- WL is programmed in the mode registers. Write data is expected WL x tCK + tDQSS after the command edge. The DM pin masks its byte on any beat of the burst.
- Back-to-back writes are spaced by tCCD = 4 clocks.
- A PRE to the same bank may follow after WL + BL/2 + RU(tWR/tCK) + 1 clocks.
- The earliest RD after a WR is WL + 1 + BL/2 + RU(tWTR/tCK) clocks after the WR command.

Key timing:

| Symbol | Rule |
| --- | --- |
| tWR | max(15 ns, 4 nCK) from last write data to PRE |
| tWTR | max(7.5 ns, 4 nCK) from last write data to RD |

## PRE - Precharge

Closes the open row of one bank or all banks.

- Encoding: CS_n low, CA0r high, CA1r high, CA2r low, CA3r high; CA4r = AB (1 = all banks); when AB = 0, CA7r-CA9r select the bank.
- After a single-bank PRE wait tRPpb; after PREab wait tRPab. tRPab is longer than tRPpb on 8-bank devices.
- PRE must not violate tRAS after ACT, tRTP after RD, or tWR after WR.

## REFab / REFpb

Refreshes rows in the storage array.

- Encoding: CS_n low, CA0r-CA2r = L L H; CA3r = H for all banks, L for per bank.
- REFab refreshes every bank and requires all banks idle; after it wait tRFCab before any ACT or further refresh.
- REFpb refreshes one bank chosen by the device's internal 0-1-...-7 counter; the target bank must be idle. After REFpb wait tRFCpb before an ACT or refresh to that bank; only tRRD is needed before an ACT to a different bank.
- The controller must track the REFpb counter; it resets after device reset, self-refresh exit, and every REFab.
- All-bank refreshes are normally issued every tREFIM = RM x tREFI, where RM comes from MR4. Up to eight refreshes may be postponed, bounding the maximum gap to 9 x tREFIM.

## Self-refresh entry and exit

- Entry: CKE falls while the REF code is on the bus and all banks are idle. Two NOPs are required after CKE goes low (tCPDED). The clock may be stopped or changed tCPDED after entry, but must be stable for at least two cycles before exit.
- Minimum stay is tCKESR.
- Exit: CKE rises asynchronously; issue NOPs until tXSR = max(tRFCab + 10 ns, 2 nCK) expires. At least one refresh (one REFab or eight REFpb) must be issued before re-entering self refresh.
- **PASR:** MR16 masks whole banks and MR17 masks eight segments per bank during self refresh. A region is retained only when both its bank mask bit and its segment mask bit are unmasked.

  | Region | Mask control | Retained in self refresh when |
  | --- | --- | --- |
  | Whole bank n | MR16 bit n | bit n = 0 |
  | Segment s of every bank | MR17 bit s | bit s = 0 |
  | Bank n, segment s | MR16 bit n and MR17 bit s | both bits = 0 |

## MRR / MRW

- MRR encoding: CS_n low, CA0r-CA3r = L L L H; register address on CA4r-CA9r and CA0f-CA1f. Burst length is fixed at 8; valid mode-register data appears on DQ0-DQ7 on the first beat, while later beats are undefined (DQ calibration patterns MR32/MR40 are the exception). DQS toggles for the full burst. tMRR = 4 clocks between MRR commands; only NOPs are allowed during tMRR.
- After idle power-down exit, wait an additional tMRRI = tRCD before MRR.
- MRW encoding: CS_n low, CA0r-CA3r = L L L L; register address on CA4r-CA9r and CA0f-CA1f, data on CA2f-CA9f. MRW is allowed only when all banks are idle; tMRW = 10 clocks, only NOPs allowed. MRW to MR63 triggers device reset and leaves array data undefined.

## Calibration and training

- **ZQ calibration:** initiated by MRW. ZQINIT runs at init; ZQCL is a long recal; ZQCS is a short periodic cal; ZQRESET returns to default. All banks must be idle, ODT disabled, and the DQ bus quiet during ZQINIT/ZQCL/ZQCS.
- **CA training:** enter via MRW to MR41, calibrate CA0-CA3/CA5-CA8, switch CA-to-DQ mapping via MR48, calibrate CA4/CA9, then exit via MR42.
- **Write leveling:** enter by setting MR2[7] high. The DRAM asynchronously feeds back the CK sample on DQ for each DQS group; the controller delays DQS until the 0-to-1 transition is found. Only NOPs or the exit MRW are allowed.
- **DQ calibration:** MRR to MR32 returns Pattern A; MRR to MR40 returns Pattern B on the designated DQ pins.

## ODT

LPDDR3 termination is asynchronous, controlled by the ODT pin and enabled by MR11[1:0]. ODT is automatically disabled during reads, self refresh, deep power-down, and CA training; it may optionally stay on during power-down via MR11[2].

## Power-down

- Entry: CKE falls with CS_n high (NOP/Deselect). Active power-down has at least one row open; idle power-down has all banks idle. No refreshes occur, so dwell time is bounded by the refresh schedule.
- CKE must not fall during MRR, MRW, RD, or WR; it may fall after ACT/PRE/REF once their timing allows.
- Exit: CKE rises with CS_n high; first valid command after tXP = max(7.5 ns, 3 nCK). At least two clock transitions must occur during tXP.

## Deep power-down

- Entry: CKE falls with the PRE code on the bus; all banks must be idle. Array contents are lost.
- The device must stay in DPD for at least tDPD = 500 us.
- Exit: CKE rises; the full power-up initialization sequence is required.

## Clock stop and frequency change

Clock stop or frequency change is allowed only when CKE is low and no ACT/PRE/RD/WR/MRW/MRR are in flight, or when CKE is high with CS_n high and all related timings (tRCD, tRP, tWR, tMRW, etc.) are satisfied. After a CKE-high change or stop, normal operation resumes only after the clock is stable for at least 2 x tCK + tXP.

## NOP / Deselect

Holds the bus idle and never aborts an in-progress operation. It is the only command legal during most power-state transitions and during tRFC/tMRW/tMRR windows.

**Source:** JESD209-3C sections 4.1-4.6, 4.7-4.8, 4.9, 4.10-4.11, 4.12, 4.13-4.16
