# TASK-004: Milestone M3 — rapids + tile working artificially (injectors/test data)

**Priority:** P1
**Status:** open -- 2026-10-19
**Owner:** sean galloway

## Why

Owner direction 2026-10-19: milestone ladder rung 3 (TILE_SPEC 12). Rapids
attaches above the roots at the tile I/O and the whole header/credit/strap
contract runs for real: 128-bit tile headers (beat-chained on the narrow
fabric links), 64 destination counters, boot advertisements, straps toward
rapids, desc packets — against injectors and synthetic test data.

## Done when

Rapids source/sink loops data through the tile on the FPGA with synthetic
traffic; credits and straps hold under sustained load (no fabric stalls
from a full sink channel); the legal-destination mask forms at boot.

## Notes

Depends on M2 (TASK-003), rapids straps (TILE_SPEC 11.9 / rapids TASK-027),
and delta delivering to level=3 (DELTA-011).
