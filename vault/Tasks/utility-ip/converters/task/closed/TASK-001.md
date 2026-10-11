# TASK-001: AXI3 converters (axi4_to_axi3 / axi3_to_axi4)

**Priority:** P2
**Status:** CLOSED 2026-10-11
**Owner:** TBD

**GitHub issue:** #96

## What

Tracking scaffolding for the AXI3 converter work: protocol converters between
AXI4 and AXI3 (`axi4_to_axi3` and `axi3_to_axi4`).

## Done when

Plan Task 11's close-out criteria.

## Resolution

Closed via GitHub issue #96. Implementation span: `2f7dd0a..3bcda2262` (21 converter commits).
Final deliverables:
- RTL: `axi4_to_axi3`, `axi4_to_axi3_rd`, `axi4_to_axi3_wr`, `axi3_to_axi4`, `axi3_to_axi4_rd`, `axi3_to_axi4_wr`, `axi3_loopback`
- DV: full converters regression passed (`168 passed, 1 xfailed` at `TEST_LEVEL=func`)
- Docs: Converters MAS v1.5 with AXI3 converter chapters + references store
