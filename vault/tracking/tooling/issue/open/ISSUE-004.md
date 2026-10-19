# ISSUE-004: hw_server partial-enumeration race refuses programming without retry

**Priority:** P3
**Status:** open
**Owner:** TBD
**Filed:** 2026-10-08
**Refs:** hit twice in one day — misc TASK-003 board leg (Genesys 2 rs_loop) and stream BUG-019 board leg (Genesys 2 obs/mon), both retried successfully

## Observation

When Vivado hw_server enumerates the JTAG chain partially — the Nexys
A7's a100t present but the Genesys 2's k325t missing (or any partial
list missing exactly the intended target) — the repo's board identity
check correctly refuses to program, but the repo's bounce-and-retry
logic (`board.py` DEVICELESS_READBACK_ATTEMPTS) only covers a FULLY
EMPTY device list. A partial enumeration therefore refuses with no
retry; a manual retry (or the next program attempt) succeeds once
hw_server sees the whole chain.

## Why it matters

Benign but expensive: each hit costs a human/agent noticing the refusal,
reading the identity failure, and re-running. Both 2026-10-08 board
sessions hit it at least once.

## Candidate disposition

Extend the bounce-and-retry to partial enumerations: if the target's
expected device idcode is absent from a NON-empty list, bounce hw_server
and retry with the same attempt budget as the empty case. Resolves into
a tooling task when someone is next in board.py.
