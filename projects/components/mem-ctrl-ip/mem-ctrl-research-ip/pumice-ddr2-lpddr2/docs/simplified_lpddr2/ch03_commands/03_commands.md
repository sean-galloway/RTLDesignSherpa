# Commands: Rules and Constraints

Each command below: what it does, its encoding, and what may follow.
Timing symbols are defined in Chapter 6.

## ACT - Activate

Opens row R of bank B (sense amps latch the row). Required before any
RD/WR to that row.

- Encoding: CA0r=L, CA1r=H; bank on CA7r-CA9r, row split across edges.
- RD/WR to the same bank may follow after tRCD.
- ACT to a different bank may follow after tRRD.
- ACT to the same bank again requires a PRE first; the ACT-PRE-ACT
  round trip must satisfy tRAS (ACT to PRE) and tRC (ACT to ACT).
- 8-bank devices only: no more than 4 ACTs in a rolling tFAW window,
  and REFpb counts as an activation for tFAW.

## RD / WR - Burst read / write

Starts a burst of BL words at column C of the open row in bank B.

- Encoding: CA0r=H, CA1r=L, CA2r = H (RD) / L (WR); AP at CA0f.
- AP=1: the bank auto-precharges after the burst (internal precharge
  starts after RL/tRAS rules for reads, after nWR for writes).
- Read data appears RL*tCK + tDQSCK + tDQSQ after the command's rising
  edge; write data is expected WL*tCK + tDQSS after the command.
- Another RD (after RD) or WR (after WR) may follow after tCCD
  (2 clocks on S4, 1 on S2). On S4 with BL4 a burst may NOT be
  interrupted; with BL8/BL16 interruption is allowed only on even clock
  cycles after the first command.
- WR after RD: at least RL + RU(tDQSCKmax/tCK) + BL/2 + 1 - WL clocks
  after the RD command (bus turnaround; see Chapter 6).
- RD after WR: at least WL + 1 + BL/2 + RU(tWTR/tCK) clocks after the
  WR command.
- PRE to the same bank may follow a RD after tRTP (min), a WR after
  tWR; tRAS must also be met.

## PRE - Precharge

Closes the open row of one bank (AB=0) or all banks (AB=1).

- Encoding: CA0r=H, CA1r=H, CA2r=L, CA3r=H; AB at CA4r.
- The bank is ready for a new ACT after tRPpb (single-bank) or tRPab
  (all-bank). On 8-bank devices tRPab is 3 ns longer; on 4-bank devices
  they are equal.
- May not be issued before tRAS after ACT, tRTP after RD, or tWR after
  WR (to that bank).

## REFab / REFpb - Refresh

REFab refreshes all banks (all must be idle); REFpb refreshes one bank,
chosen by the device's internal round-robin counter (0-1-...-7-0-...).

- Encoding: CA0r=L, CA1r=L, CA2r=H; CA3r = H (all) / L (per bank).
- REFpb is 8-bank devices only; the target bank must be idle, and the
  controller must track the round-robin position (it resets to bank 0
  on reset, on self-refresh exit, and on every REFab).
- After REFab: wait tRFCab before any ACT or further REF. After REFpb:
  wait tRFCpb before an ACT to the same bank or another REF; only tRRD
  before an ACT to a different bank.
- During REFpb the other banks stay fully usable - that is its purpose.

## BST - Burst terminate

Truncates the most recent RD or WR burst.

- Encoding: CA0r=H, CA1r=H, CA2r=L, CA3r=L.
- Legal only within BL/2 - 1 clocks after the RD/WR command (S4); on
  S2 it may be issued in any cycle after the command.
- Effective burst length after BST = 2 x (clocks from RD/WR to BST).
  Use the effective BL in all subsequent turnaround math.
- The truncation takes effect one full read/write latency later.

## MRW / MRR - Mode register write / read

- MRW: all banks must be idle; no command other than NOP for tMRW
  (5 clocks) after. Any MRW to MR63 is a device Reset.
- MRR: fixed BL4; register contents appear on DQ0-DQ7 of the first beat
  only (later beats undefined); DQS toggles for the whole burst; the
  operation may not be interrupted; tMRR = 2 clocks between commands.
- MRR may not be issued earlier than BL/2 after a RD, or
  WL + 1 + BL/2 + RU(tWTR/tCK) after a WR.

## Self-refresh entry / exit

- Entry: CKE falls with the REF encoding, all banks idle. The device
  refreshes itself from an internal timer; all inputs except CKE become
  don't-care; VDDQ may be powered down.
- Minimum stay tCKESR; the clock may be stopped or re-tuned one clock
  after entry, but must be stable 2 clocks before exit.
- Exit: CKE rises (asynchronous); NOPs until tXSR (= tRFCab + 10 ns)
  expires. At least one refresh (1 REFab or 8 REFpb) must be issued
  after exit before the next self-refresh entry.

## Power-down (PD)

- Entry: CKE falls with CS_n high (or NOP). With all banks idle it is
  idle PD; with a row open it is active PD. Input/output buffers (except
  CK and CKE) shut down; no refreshes occur, so dwell time is bounded by
  the refresh requirement.
- Minimum stay tCKE; exit on CKE rise with CS_n high; first valid
  command after tXP.

## Deep power-down (DPD)

- Entry: CKE falls with the PRE encoding, all banks idle. Nearly
  everything inside the device powers down; array contents may be lost.
- Minimum stay tDPD = 500 us. Exit on CKE rise, then the full
  initialization sequence (from the tINIT3 NOP wait) is mandatory.

## NOP / Deselect

Keeps the bus idle; never aborts anything. Mandatory after power-state
entries/exits and wherever no other command is legal.

**Source:** JESD209-2F sections 5.1, 5.3-5.7, 5.9-5.15, 5.17
