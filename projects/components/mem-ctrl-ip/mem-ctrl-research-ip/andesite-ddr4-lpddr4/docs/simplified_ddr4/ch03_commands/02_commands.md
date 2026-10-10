# Commands: Rules and Constraints

What each command does and what must come next. Timing symbols are defined in Chapter 6; examples use the drill model (BG0 = B0-B3, BG1 = B4-B7, R0-R7, C0-C7).

## ACT - Bank Activate

Opens row R in bank B so reads and writes can follow.

- ACT -> RD/WR same bank: wait tRCD, unless additive latency posts the command. With AL > 0 the RD/WR can be issued immediately, but internal CAS must not occur before tRCD.
- ACT -> ACT different bank group: tRRD_S.
- ACT -> ACT same bank group, different bank: tRRD_L.
- ACT -> ACT same bank: tRC (= tRAS + tRP), and the prior row must already be precharged.
- ACT -> PRE same bank: tRAS (the open row must remain active long enough).
- At most 4 ACTs in any rolling tFAW window. tFAW is independent of bank group.

## RD / RDA - Read

Burst read starting at the given column. Data appears RL = AL + CL + PL clocks after the command, where PL is the CA parity latency if enabled. DQS begins toggling one or two cycles before the first data, selected by MR4 A[12:11] (1tCK or 2tCK read preamble).

- RD -> RD (different bank group): tCCD_S = 4 clocks.
- RD -> RD (same bank group): tCCD_L, programmed in MR0 A[12:10] (5-8 clocks depending on speed grade).
- RD -> PRE same bank: earliest spacing is AL + tRTP, also bounded by tRAS. tRTP = max(4 nCK, 7.5 ns).
- RDA (A10/AP = 1): auto-precharge starts internally after AL + tRTP, delayed if tRAS has not been met. Next ACT to that bank needs tRP from when precharge starts and tRC from the old ACT.
- RD -> WR (book symbol tRTW): JESD79-4D does not name tRTW; the figures give the command spacing as RL + BL/2 + 2 - WL clocks. For BL8 this is RL + tCCD_S + 2 - WL; for BC4 it is RL + tCCD_S/2 + 2 - WL.

## WR / WRA - Write

Burst write. The first data is captured WL = AL + CWL + PL clocks after the command. DQS must satisfy tDQSS relative to CK.

- WR -> WR (different bank group): tCCD_S = 4 clocks.
- WR -> WR (same bank group): tCCD_L.
- WR -> RD: wait until the last write data has been absorbed and tWTR has passed. tWTR_S applies to different bank groups; tWTR_L applies to the same bank group. The reference point is the first rising CK after the last write data.
- WR -> PRE same bank: WL + BL/2 + tWR. tWR is the write recovery time (15 ns minimum, programmed in MR0 A[13,11:9]); violating it corrupts data.
- WRA (A10/AP = 1): internal auto-precharge starts after write recovery. The bank can be re-activated once (WRA + tRP) and tRC are met.
- Write CRC (MR5 A12 = 1): adds one UI to the write burst and extends WL by 1. When both CRC and DM are enabled, use tWR_CRC_DM and tWTR_S_CRC_DM / tWTR_L_CRC_DM in place of the normal values.
- Write DBI and DM cannot both be enabled.

## PRE / PREA - Precharge

Closes the open row and restores data to the array. A10/AP = 0 closes the bank selected by BG/BA; A10/AP = 1 closes all banks.

- PRE -> ACT same bank: tRP.
- Illegal if it would truncate a burst still in flight.

## REF - Refresh

One internal refresh step across all banks; the address counter is internal.

- Precondition: all banks precharged and tRP met.
- REF -> ACT or REF: tRFC (density-dependent).
- Fine granularity refresh (FGR) modes: 1x (tRFC1, tREFI1 = 7.8 us), 2x (tRFC2, tREFI2 = 3.9 us), and 4x (tRFC4, tREFI4 = 1.95 us) at normal temperature. Program MR3 A[8:6] for fixed or on-the-fly selection; REF encoding with BG0 selects the rate in on-the-fly mode.
- Scheduling slack for 1x mode: up to 8 REFs may be postponed (max gap 9 x tREFI), and up to 8 may be pulled in early. Scaling applies to 2x and 4x modes.
- DDR4 does not define per-bank refresh; every REF refreshes all banks.

## Self-refresh entry / exit

Entry: REF encoding with CKE falling, all banks idle, ODT off. The DRAM keeps itself refreshed without needing CK; only CKE matters.

- Minimum stay: tCKESR, plus an internal refresh occurs within tCKE of entry.
- Exit: CK must be stable before CKE rises. DES during the exit window.
- tXS after exit before any non-read command; tXSDLL before any command that needs a locked DLL (RD/RDA). tXS = tRFC(min) + 10 ns.
- MR4 A9 selects self-refresh abort mode: when enabled, use tXS_Abort (tRFC4(min) + 10 ns) and the DRAM aborts any ongoing refresh without incrementing the counter.
- Before re-entering self-refresh, issue at least one REF.
- LP ASR (MR2 A[7:6]) selects the self-refresh temperature range.

## Power-down

CKE low with DES. Two flavors: precharge PD (all banks closed) and active PD (a row open). The DLL is kept on in both cases.

- Exit to any valid command: tXP. tXP = max(4 nCK, 6 ns) for DLL-on exit.
- CKE low pulse must satisfy tCKE. The CKE transition windows need DES coverage (tCPDED).
- PD performs no refresh; stay bounded by refresh requirements, at most 9 x tREFI.
- Entry is not allowed during MRS, MPR, ZQCAL, DLL lock, or read/write; it is allowed during activation, precharge/auto-precharge, and refresh once those operations complete.

## NOP and DES

Bus fillers. NOP keeps CS_n low; DES raises CS_n. Neither changes state. Use them to occupy forced gaps (tRRD, tCCD, turnaround bubbles, tCPDED windows).

## RESET

RESET# low is an asynchronous override. It resets the device, aborts any operation, and forces outputs to High-Z. After RESET# rises the normal power-up or stable-power reset sequence must be followed (200 us at power-up or 100 us with stable power, then 500 us before CKE high, etc.). ODT is High-Z while RESET# is asserted and until CKE is registered high. tXPR = max(5 nCK, tRFC(min) + 10 ns).

## MRS / mode-register updates

MRS writes MR0-MR6. All address fields of the target register are rewritten, even if only a subset changes.

- MRS -> MRS: tMRD (8 nCK).
- MRS -> any non-NOP/DES command: tMOD = max(24 nCK, 15 ns).
- MRS must be issued when all banks are idle, all bursts complete, and CKE high. If RTT_NOM is enabled, ODT must be held low before and during the MRS command until tMOD expires.
- DLL reset (MR0 A8 = 1) needs tMOD and then tDLLK before DLL-dependent commands.
- With CAL enabled, use tMOD_CAL = tMOD + tCAL and tMRD_CAL = tMOD + tCAL.

## DLL-off mode and DLL on/off switching

DLL-off is entered by clearing MR1 A0. Maximum clock frequency is tCKDLL_OFF; CL=10 and CWL=9 are the required settings. CA parity is not allowed with DLL off. Read data timing uses RL = AL + (CL - 1) and a larger tDQSCK window. Switching DLL state requires entering self-refresh, changing frequency, and meeting tCKSRE/tCKSRX/tXS before normal commands resume.

## Input clock frequency change

The clock may change only during self-refresh. Hold ODT and CKE low, wait tCKSRE after CKE falls, change frequency, provide a stable clock for tCKSRX, then exit. After exit and tXS, update CL/CWL/WR/gear-down/preamble/CAL/parity settings as needed. CA parity latency must be disabled before the frequency change and re-enabled afterward.

## Write leveling entry / exit

Used to align DQS-DQS# to CK-CK# across fly-by routing.

- Entry: MRS to MR1 with A7 = 1; output buffers of other ranks disabled via MR1 A12 = 1. Only DES and another MRS are valid in leveling mode.
- The DRAM asynchronously feeds back the sampled CK level on DQ. The controller sweeps DQS delay until it sees a 0 -> 1 transition.
- Exit: stop driving DQS, drive ODT low, then MRS MR1 with A7 = 0. Wait tMOD before normal commands; MRS-to-MRS spacing is tMRD.

## MPR read flow

The Multi-Purpose Register outputs a predefined calibration pattern or accepts training writes.

- Precharge all banks and wait tRP.
- MRS to MR3 with A2 = 1 (and A[1:0] selecting the page) to enter MPR mode.
- Wait tMRD and tMOD.
- Issue RD/RDA with A[1:0] = 00 and A2 = 0 for BL8; only RD/RDA/WR/WRA/DES/REF/MRS/RESET are legal in MPR mode. RDA/WRA behave like plain reads/writes (auto-precharge ignored). Only 1x refresh is allowed.
- After the last MPR burst, wait tMPRR, then MRS to MR3 with A2 = 0 to exit.
- Wait tMRD and tMOD before normal array commands.

## Gear-down mode

Gear-down (2N command timing) is selected by MR3 A3. It can only be entered during initialization or after self-refresh exit. The sequence is: a low-frequency 1N MRS to set MR3 A3 = 1, then a 1N sync pulse (NOP) lasting an even number of clocks, then normal 2N operation after tCMD_GEAR. CL, CWL, WR/RTP, AL, CAL and PL must all be programmed to even values. CAL and CA parity must be disabled before the gear-down MRS and can be re-enabled after tSYNC_GEAR and tCMD_GEAR. Self-refresh resets the DRAM back to 1N mode.

## CAL mode

Command Address Latency (CAL) is a power-saving feature controlled by MR4 A[8:6]. CS_n is asserted tCAL cycles before the command/address is valid, giving the DRAM time to enable its receivers. Valid settings are 3, 4, 5, 6, and 8 clocks. With CAL enabled, MRS-to-command spacing becomes tMOD_CAL = tMOD + tCAL and MRS-to-MRS spacing becomes tMRD_CAL = tMOD + tCAL. In geardown mode, odd CAL values are rounded up to the next even integer.

## CRC error handling

Write CRC is enabled by MR5 A12. The DRAM compares the received checksum against its own calculation. On mismatch it drives ALERT# low for at least 6 clocks (CRC ALERT_PW) within tCRC_ALERT (max 13 ns). It also sets MR5 A3 (CRC Error Clear) and a status bit in MPR page 1. The controller must retry the write and maintain coherence. CRC and DM together block the write to the array on error; with CRC alone the DRAM may write bad data, so the controller retries.

## CA parity error handling

Turn on CA parity by writing a non-zero parity latency (PL) into MR5 A[2:0]. The PAR bit covers ACT_n, RAS/A16, CAS/A15, WE/A14, BG, BA, and A[17:0]; unused address pins are treated as 0 inside the DRAM. The parity convention is even. After detecting a parity error the DRAM drops the bad command, drives ALERT# low for at least tPAR_ALERT_PW, records the errant frame in MPR page 1, sets MR5 A4 (Parity Error Status), precharges all banks once tRAS_min is satisfied, and accepts normal commands again only after the status bit is cleared. With persistent parity error mode enabled (MR5 A9 = 1), parity checking resumes automatically once the alert pulse ends.

**Source:** JESD79-4D sections 4.1, 4.2, 4.4, 4.6, 4.7, 4.9, 4.10, 4.11, 4.12, 4.15, 4.16, 4.17, 4.18, 4.19, 4.22, 4.23, 4.24, 4.25, 4.26, 4.27, 4.28
