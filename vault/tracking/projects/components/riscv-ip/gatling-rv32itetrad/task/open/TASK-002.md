# TASK-002 — gatling RTL bring-up: barrel model chapter, RTL, HAS/MAS

**Status:** open · **Priority:** high · **Filed:** 2026-10-19 · **Area:** projects/components/riscv-ip/gatling-rv32itetrad

## Why

Gatling is PRD-only (v0.2): no RTL, and `docs/gatling_has/`,
`docs/gatling_mas/`, `docs/barrel_model/` are stubs. It is on the critical
path for tile milestone M1 (tetrad on the FPGA — tile TASK-002). Per the
2026-10-19 owner ruling, gatling sequences the four alu-infer ALUs of its
adjacent cells via POP/PUSH/FLUSH; the program is the schedule.

## What

1. `docs/barrel_model/` study chapter first (PRD 8.1: "writes first — it is
   the justification"): the kestrel-cost -> interleave-fix argument for the
   4-context barrel.
2. Gatling RTL: 4-state F/D/X/W barrel, 4 context PCs + register files,
   shared ALU/decoder/Xcell unit, POP/PUSH/CFG/ECTX/FLUSH/KICK/WAIT
   (custom-0 0x0B, PRD 3.1 v0.2), per-context MonBus status (active, stall
   reason, done).
3. HAS + MAS stubs fill in as the RTL lands (PRD 8.2/8.3).
4. Hand-assembled hex for bring-up programs; binutils fragment later
   (PRD 7, non-blocking).

## Done when

Gatling RTL runs a hand-assembled tetrad program in DV: four contexts POP
operands into the cell ALU issue handshake, PUSH results, FLUSH drains to a
programmed destination; func+gate green; HAS/MAS no longer stubs.

## Notes

Sequenced after the cell works standalone (cell TASK-001/002) — the cell is
the lowest module, owner direction 2026-10-18. Confirm the PRD 7 leanings
(gatling TASK-001) before the RTL freezes them.
