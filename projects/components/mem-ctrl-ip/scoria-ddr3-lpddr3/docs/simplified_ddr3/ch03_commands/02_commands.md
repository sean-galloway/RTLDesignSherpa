# Commands: Rules and Constraints

What each command does and what must come next. Timing symbols are defined in Chapter 6; examples use the drill model (B0-B7, R0-R7, C0-C7).

## ACT - Bank Activate

Opens row R in bank B so reads and writes can follow.

- ACT -> RD/WR same bank: wait tRCD, unless additive latency posts the command. With AL > 0 the RD/WR can be issued immediately, but internal CAS must not occur before tRCD.
- ACT -> ACT different bank: tRRD.
- ACT -> ACT same bank: tRC (= tRAS + tRP), and the prior row must already be precharged.
- ACT -> PRE same bank: tRAS (the open row must remain active long enough).
- On 8-bank devices: at most 4 ACTs in any rolling tFAW window.

## RD / RDA - Read

Burst read starting at the given column. Data appears RL = AL + CL clocks after the command. DQS begins toggling one cycle before the first data (read preamble).

- RD -> RD (any bank): tCCD = 4 clocks; back-to-back reads can be issued every tCCD.
- RD -> PRE same bank: earliest spacing is AL + tRTP, also bounded by tRAS. tRTP.MIN = max(4 nCK, 7.5 ns).
- RDA (A10=1): auto-precharge starts internally after the same AL + tRTP delay, delayed if tRAS has not been met. Next ACT to that bank needs tRP from when precharge starts and tRC from the old ACT.
- RD -> WR (book symbol tRTW): the spec does not name tRTW; the figures give the command spacing as RL + BL/2 + 2 - WL clocks. For BL8 this is RL + tCCD + 2 - WL; for BC4 it is RL + tCCD/2 + 2 - WL.

## WR / WRA - Write

Burst write. The first data is captured WL = AL + CWL clocks after the command. DQS must satisfy tDQSS relative to CK.

- WR -> WR (any bank): tCCD = 4 clocks.
- WR -> RD: wait until the last write data has been absorbed and tWTR has passed. tWTR is measured from the first rising CK after the last write data.
- WR -> PRE same bank: WL + BL/2 + tWR. tWR is the write recovery time programmed in MR0; violating it corrupts data.
- WRA (A10=1): internal auto-precharge starts after write recovery. The bank can be re-activated once (WRA + tRP) and tRC are met.
- DM masks individual bytes during writes. DDR3 has no DBI or write parity.

## PRE / PREA - Precharge

Closes the open row and restores data to the array. A10=0 closes the bank selected by BA; A10=1 closes all banks.

- PRE -> ACT same bank: tRP. Unlike DDR2, DDR3 does not add an extra clock for PREA; both use the same tRP.
- Illegal if it would truncate a burst still in flight.

## REF - Refresh

One internal refresh step across all banks; the address counter is internal.

- Precondition: all banks precharged and tRP met.
- REF -> ACT or REF: tRFC (density-dependent).
- Average refresh interval tREFI = 7.8 us at case temperatures up to 85C; 3.9 us in the optional extended range (85C to 95C).
- Scheduling slack: up to 8 REFs may be postponed, so the largest gap between two REFs is 9 x tREFI. Up to 8 REFs may be pulled in early; at most 16 REFs may occur within any 2 x tREFI window.

## Self-refresh entry / exit

Entry: REF encoding with CKE falling, all banks idle, ODT off. The DRAM keeps itself refreshed without needing CK; only CKE matters.

- Minimum stay: tCKE, plus an internal refresh occurs within tCKE of entry.
- Exit: CK must be stable before CKE rises. NOP/DES during the exit window.
- tXS after exit before any non-read command; tXSDLL before any command that needs a locked DLL (such as RD). The DDR3 spec names these tXS/tXSDLL (not tXSR/tXSRD).
- Before re-entering self-refresh, issue at least one REF.
- SRT (MR2 A7) and optional ASR (MR2 A6) select the self-refresh temperature range.

## Power-down

CKE low with NOP/DES. Two flavors: precharge PD (all banks closed) and active PD (a row open).

- Precharge PD has fast exit (MR0 A12 = 1, DLL kept on) and slow exit (MR0 A12 = 0, DLL off).
- Active PD always uses fast exit; the DLL stays on.
- Exit to any valid command: tXP. After slow precharge PD exit, commands needing the DLL (RD, RDA, ODT-controlled transitions) wait tXPDLL.
- CKE low pulse must satisfy tCKE. The CKE transition windows need NOP/DES coverage (tCPDED).
- PD performs no refresh; stay bounded by refresh requirements, at most 9 x tREFI if 8 REFs were posted beforehand.

## NOP and DES

Bus fillers. NOP keeps CS low; DES raises CS. Neither changes state. Use them to occupy forced gaps (tRRD, tCCD, turnaround bubbles, tCPDED windows).

## RESET

RESET# low is an asynchronous override. It resets the device, aborts any operation, and forces outputs to High-Z. After RESET# rises the normal power-up or stable-power reset sequence must be followed (200 us at power-up or 100 us with stable power, then 500 us before CKE high, etc.). ODT is High-Z while RESET# is asserted and until CKE is registered high.

## MRS / mode-register updates

MRS writes MR0-MR3. All address fields of the target register are rewritten, even if only a subset changes.

- MRS -> MRS: tMRD.
- MRS -> any non-NOP/DES command: tMOD.
- MRS must be issued when all banks are idle, all bursts complete, and CKE high. If RTT_NOM is enabled, ODT must be held low before and during the MRS command until tMOD expires.
- DLL reset (MR0 A8 = 1) needs tMOD and then tDLLK before DLL-dependent commands.

## Frequency change in precharge power-down

The input clock frequency may only change during self-refresh or precharge power-down. In precharge PD: hold ODT and CKE low, wait tCKSRE after CKE falls, change frequency, provide a stable clock for tCKSRX, then exit PD. After exit and tXP, reset the DLL via MRS and update CL/CWL/WR as needed. RTT_NOM must be disabled or ODT held low during the frequency change.

## Write leveling entry / exit

Used to align DQS-DQS# to CK-CK# across fly-by routing.

- Entry: MRS to MR1 with A7 = 1, output buffers of other ranks disabled via MR1 A12 = 1. Only NOP/DES and another MRS are valid in leveling mode.
- The DRAM asynchronously feeds back the sampled CK level on DQ. The controller sweeps DQS delay until it sees a 0 -> 1 transition.
- Exit: stop driving DQS, drive ODT low, then MRS MR1 with A7 = 0. Wait tMOD before normal commands; MRS-to-MRS spacing is tMRD.

## MPR read flow

The Multi-Purpose Register outputs a predefined calibration pattern.

- Precharge all banks and wait tRP.
- MRS to MR3 with A2 = 1 (and A[1:0] selecting the pattern) to enter MPR mode.
- Wait tMRD and tMOD.
- Issue RD/RDA with A[1:0] = 00 and A2 = 0 for BL8; only RD/RDA are legal in MPR mode. RDA behaves like a plain read (auto-precharge is ignored).
- After the last MPR burst, wait tMPRR, then MRS to MR3 with A2 = 0 to exit.
- Wait tMRD and tMOD before normal array commands.

**Source:** JESD79-3F sections 3.3, 3.4.1, 4.7, 4.8, 4.10, 4.11, 4.12, 4.13, 4.14, 4.15, 4.16, 4.17
