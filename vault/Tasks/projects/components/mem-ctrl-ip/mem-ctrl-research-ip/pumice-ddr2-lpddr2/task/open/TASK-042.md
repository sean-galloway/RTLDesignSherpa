# TASK-042: LPDDR2 board enablement — from "vaguely supported" to fully enabled

> Source: owner, 2026-10-04 — an LPDDR2 board is coming; the combined
> DDR2/LPDDR2 controller should be fully enabled for it.
> Related: MC-001 (memory-controllers lane) — the runtime-ZQ block this
> task creates lands in `pumice_training_layer`, per the owner's 2026-10-04
> training-layer ruling recorded there.

**Priority:** P1 (board-driven)
**Status:** open
**Owner:** TBD

Pumice's LPDDR2 support today is real but init-centric: the init sequencer
runs the JEDEC LPDDR2 MRW chain (Reset -> ZQ(MR10) -> MR1 -> MR2 -> MR3),
and `refresh_ctrl` carries the REFpb (per-bank) framework. Both memtypes
pass the simulation suite at block level. What a working board needs that
does not exist yet:

- [ ] **Runtime ZQ calibration.** LPDDR2 ZQ today happens once at init
  (MRW(MR10) = ZQINIT). JESD209-2 expects ZQCS/ZQCL maintenance over
  temperature/voltage drift. Build the runtime block: interval CSR,
  MRW-sequenced ZQCS/ZQCL issue through the existing maintenance channel,
  placement-policy discipline carried from the family posture. This block
  is the natural first content of `pumice_training_layer` (owner ruling,
  MC-001) — born there rather than inside the scheduler layer.
- [ ] **Board timing/CSR definition.** CSR timing values for the actual
  LPDDR2 part (tINIT1/2/4, tZQINIT, tREFI/pb, tRFC/pb, CA latencies) from
  the part's JESD209-2 speed bin; DDR2 side stays as-is. Includes the
  `PHY_TIMING.memtype` runtime-select validation on both settings.
- [ ] **BFM/DV gap check.** Verify the in-house BFM (RTLDesignSherpa-DV)
  models LPDDR2 behavior beyond init: REFpb acceptance, MRW(CA-bus)
  decoding per JESD209-2, ZQ command effects. File DV-repo gaps the way
  andesite TASK-010 did for DDR4/LPDDR4 (G1-G5 pattern).
- [ ] **Board bring-up harness.** Top-level harness + constraints for the
  board (pinout, reset polarity, clocking), a DDR2-vs-LPDDR2 bring-up
  checklist, and an RTL-sim smoke against the BFM's LPDDR2 mode before
  hardware.
- [ ] **REFpb runtime exercise.** The REFpb framework is ported but
  board-unproven: run per-bank refresh in traffic on the BFM, then on the
  board, and confirm the bank-rotor mirror stays synchronized (the
  carried suite proves the mechanics; the board proves the device).

Closes when the board boots LPDDR2 through init, runs traffic with runtime
ZQ + REFpb active, and the DDR2 path still passes its suite unchanged.
