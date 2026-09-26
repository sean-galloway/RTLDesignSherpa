# TASK-002: run the inherited monitor suites against the lite with per-class skips

**Priority:** P3
**Status:** open
**Owner:** TBD
**Related:** amba/monitor-lite TASK-001 section 6 (the verification contract that named these suites)

TASK-001's contract said the existing monitor suites are the lite's contract,
run through the same wrappers with `MONITOR_LITE=1`: `test_axi4_monitor`,
`test_axi_monitor_runtime_disable`, `test_axi_monitor_soak`,
`test_axi_monitor_wr_same_cycle`, `test_axi_mon_block_ready` (inverted),
`test_axi_monitor_pktgen`'s timeout starvation. They were NOT run. They assert
on packet classes the lite does not emit (perf, debug, addr-match) and on
`block_ready`, which the lite never asserts, so each needs a per-class skip
or an inverted expectation keyed on the wrapper parameter before it means
anything.

**Done when:** each suite listed has a `MONITOR_LITE=1` cell in its REG_LEVEL
grid, the lite-inapplicable checks are skipped by class (not by file), and
the run is green at full with a count of checks performed, not just a
verdict (handbook: checker-verdict-needs-a-count).
