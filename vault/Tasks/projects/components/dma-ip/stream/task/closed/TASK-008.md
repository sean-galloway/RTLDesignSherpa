# TASK-008: perf FIFO is read non-empty, pairing asserted
> **Was `TASK-086` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** CLOSED 2026-09-23  **Priority:** Medium

`dv/tests/top/test_stream_top_perf.py` drives a transfer so perf_profiler
captures scheduler idle transitions, then asserts the pop protocol (LOW alone
must not pop; either order retires exactly one entry) AND data coherence (a
captured entry carries a non-zero timestamp; one transfer yields exactly one
START and one END, START earlier).

The coherence half is what gives it teeth. The FIRST version asserted only
the pop protocol and PASSED against the old datapath -- exactly the worthless
test this task existed to prevent. Measured both directions, forced rebuild:

| RTL | time | result |
|---|---|---|
| current | 248.90s | 1 passed -- `pairing OK: START@0x3E -> END@0x93` |
| old datapath | 211.59s | 1 failed -- `PERF_DATA_LOW returned 0` |

Vacuous-pass guards: PERF_STATUS must be non-empty before any read, and
PERF_CONFIG must read back with PERF_EN set (`cfg_perf_enable` is ANDed with
GLOBAL_EN in stream_config_block). Registers addressed by name throughout.
Auto-discovered by `run-all-*` (`TESTS := wildcard test_*.py`).

Known scope, not hidden: the scenario yields 2 entries (one START/END pair);
sustained pairing over many entries is untested. The negative run is a hybrid
(old perf_profiler + current top) because a true pre-change checkout no
longer elaborates -- it isolates the datapath, which is what 45fa4972e
changed.

---
