# TASK-002: run the inherited monitor suites against the lite with per-class skips

**Priority:** P3
**Status:** CLOSED 2026-09-28
**Owner:** TBD
**Related:** amba/monitor-lite TASK-001 section 6 (the verification contract that named these suites)

TASK-001's contract said the existing monitor suites are the lite's contract,
run through the `_monlite` wrappers: `test_axi4_monitor`,
`test_axi_monitor_runtime_disable`, `test_axi_monitor_soak`,
`test_axi_monitor_wr_same_cycle`, `test_axi_mon_block_ready` (inverted),
`test_axi_monitor_pktgen`'s timeout starvation. They were NOT run. They assert
on packet classes the lite does not emit (perf, debug, addr-match) and on
`block_ready`, which the lite never asserts, so each needs a per-class skip
or an inverted expectation keyed on the wrapper parameter before it means
anything.

**Done when:** each suite listed has a `_monlite` DUT cell in its REG_LEVEL
grid, the lite-inapplicable checks are skipped by class (not by file), and
the run is green at full with a count of checks performed, not just a
verdict (handbook: checker-verdict-needs-a-count).

---

## CLOSED 2026-09-28

Every suite named above has lite cells in its own grid, run green at GATE
from clean builds after the RTL change below, with the count of checks in the
log rather than a bare verdict:

| Suite | Lite cells | Result |
|---|---|---|
| `test_axi4_monitor` (core, `axi_monitor_lite`) | 6 | 6/6 phases each; the 11 base cells re-run with the guarded TB, 17/17 |
| `test_axi_monitor_wr_same_cycle` | 2 (+2 base) | 4/4 after the fix; a fifth phase (partial early burst) added for both cores |
| `test_axi_monitor_runtime_disable` | 1 (+1 base) | 2/2; leak oracle on the lite is `refused_count == 0` |
| `test_axi_mon_block_ready` | 16 on 11 wrappers | 40/40 with the 24 full-monitor cells; `LiteRefuseCheck` (new, beside `BlockReadyCheck`) |
| `test_axi_monitor_soak` | 1 | 60k and 200k cycles: generated == delivered + reported + pending, exactly |
| `test_axi_monitor_pktgen` | 2 (starvation) | accounting exact; timeout LOST at 1 error/cycle, delivered at 1-in-2 |
| `val/amba/monitor-lite` area | 108 | GATE from `make clean-all`, 108/108 |
| `formal/amba/axi_monitor_lite` | prove + cover | PASS after the fix |

Nothing was skipped by file. Where the lite has no full-monitor signal the
check became the lite's own contract: `block_ready` -> `refused_count`
accounting (`admitted == transaction_count + refused_count + live`), perf and
debug classes -> the cfg pins are simply not driven (`_drive()` guards in the
shared TBs), the table probe -> the `active_count` port.

**Two RTL defects found and fixed in `axi_monitor_lite.sv`:**
1. A W beat in the same cycle as its AW (no AW awaiting data) was counted as
   early data while the new entry queued for beats already gone; the B then
   reported `RESP_ORPHAN`, the entry stayed live and the stale early count
   poisoned the next write (`LAST_MISSING`). Same-cycle beats are now absorbed
   at allocation, the mirror of BUG-037's fix in the full core.
2. The absorbed early-beat count was off by one (`cmd_len - e + 1` for `cmd_len - e`):
   a legal two-beat write with one early beat reported `BURST_LENGTH`.

**Measured, filed, not fixed:** monitor-lite TASK-004 -- a timeout is a
one-cycle scan pulse that loses the one-per-cycle pick to an Error, so under a
sustained error stream it is counted as dropped rather than delivered.

**Stimulus facts recorded (bus-level counting in `LiteRefuseCheck`):** the
AXI-Lite master BFMs keep at most 4 reads / 2 writes in flight and the AXI5
and AXI4-slave read BFMs at most 4, so the full wrappers' occupancy of 7 at
depth 8 in this suite was their own retire latency; each lite cell's depth is
set from that measurement, and `axil4_master_wr_monlite` is not claimed
because its core taps behind the write skid and never sees two outstanding.
