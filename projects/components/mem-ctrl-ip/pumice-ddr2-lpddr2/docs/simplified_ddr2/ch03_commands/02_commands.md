# Commands: Rules and Constraints

Each command, what it does, and what it forbids next. Timing symbols are
defined in Chapter 6; the drill model (B0-B7, R0-R7, C0-C7) is used for
examples.

## ACT - Bank Activate

Opens row R in bank B (row copied to the bank's sense amps). Required
before any RD/WR to that bank.

- ACT -> RD/WR same bank: wait tRCD, unless additive latency absorbs it.
  With AL > 0 the RD/WR may be issued immediately ("posted") and the DRAM
  holds it for AL clocks; AL must still be chosen so internal CAS lands no
  earlier than tRCD.
- ACT -> ACT different bank: tRRD.
- ACT -> ACT same bank: tRC (= tRAS + tRP), and the bank must have been
  precharged first.
- On 8-bank parts: at most 4 ACTs in any rolling tFAW window.
- ACT -> PRE same bank: tRAS (row must stay open long enough to restore).

## RD - Read (A10=0)

Burst read of BL words starting at the given column. Data appears RL =
AL + CL clocks after the command; DQS goes low one clock before data
(read preamble).

- RD -> RD (any bank): tCCD = 2 clocks; seamless back-to-back every BL/2
  clocks.
- RD -> WR: read-to-write turnaround, BL/2 + 2 clocks command spacing
  (4 clocks at BL4, 6 at BL8), so the write preamble does not collide
  with the read burst.
- RD -> PRE same bank: earliest at AL + BL/2 + max(RTP, 2) - 2 clocks;
  also bounded by the analog tRTP from the last 4-word prefetch, and by
  tRAS from the ACT.
- RDA (A10=1): the bank auto-precharges; the precharge begins (AL + BL/2)
  clocks after the command, delayed internally until tRAS and tRTP are met.
  Next ACT to that bank: tRP after precharge actually starts, and tRC from
  the old ACT.

## WR - Write (A10=0)

Burst write; first data is strobed in WL = RL - 1 clocks after the
command. Write data must respect tDQSS (DQS aligned to CK).

- WR -> WR (any bank): tCCD = 2 clocks; seamless every BL/2 clocks.
- WR -> RD: CL - 1 + BL/2 + tWTR clocks after the WR command. tWTR covers
  moving the last write data from the input buffer into the sense amps -
  it is not the same thing as write recovery.
- WR -> PRE same bank: WL + BL/2 + tWR. tWR (write recovery) lets the
  last data be written into the array before the row closes. tWR is
  programmed in clocks via MR; violating it corrupts data.
- WRA (A10=1): auto precharge starts after write recovery; the bank may be
  re-activated once (WR + tRP) - the tDAL combination - and tRC are met.

## PRE / PREA - Precharge

Closes the open row, restoring data to the array. A10=0 closes the bank
selected by BA; A10=1 closes all banks.

- PRE -> ACT same bank: tRP. On 8-bank parts, PREA gets one extra clock:
  tRPall = tRP + 1 tCK.
- Illegal while a burst it would truncate is still in flight (see RD/WR
  rules above).

## REF - Refresh

One internal refresh step across all banks; address counter is internal.

- Precondition: all banks precharged and tRP met.
- REF -> ACT or REF: tRFC (density-dependent, 75-327.5 ns).
- Average rate tREFI = 7.8 us (3.9 us above 85 C case, optional mode).
- Scheduling slack: up to 8 REFs may be postponed ("posted"), so the worst
  gap between two REFs is 9 x tREFI.

## Self-refresh entry / exit

Entry: REF encoding with CKE falling, all banks idle, ODT off. The DRAM
keeps itself refreshed with the external clock ignored; only CKE matters.

- Minimum stay: tCKE (3 clocks).
- Exit: clock must be stable first, then CKE high. NOP/DES during the exit
  window. tXSNR (= tRFC + 10 ns) before any non-read command; tXSRD (200
  clocks) before a read - the DLL is re-locking.
- Before re-entering self-refresh, issue at least one REF (a refresh may
  have been missed at the exit boundary).
- PASR (EMR2) limits refresh to a fraction of the array; data outside it
  is lost on entry.

## Power-down

CKE low with NOP/DES. Two flavors: precharge PD (all banks idle; DLL off)
and active PD (a row open). Active PD has two exit modes selected by MR
A12: fast exit (tXARD = 2 clocks, DLL kept on) and slow exit (tXARDS =
6-AL clocks, lower power, DLL off).

- Exit to any non-read command: tXP = 2 clocks.
- CKE low pulse must be at least tCKE.
- PD performs no refresh: duration is bounded by refresh requirements,
  9 x tREFI at best with 8 REFs posted beforehand.

## NOP and DES

Bus fillers. NOP keeps CS low (command bus active); DES raises CS. Neither
changes state. Used to occupy forced gaps (tRRD, tCCD, turnaround bubbles).

## Interrupts

BL4: no interruption of any kind. BL8: a read may be interrupted by a read,
a write by a write, only at the 4-word boundary. Cross-direction or
misaligned interruption is illegal.

**Source:** JESD79-2F sections 3.5-3.11, 3.15, 3.16
