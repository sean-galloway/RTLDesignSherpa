# converters — task rollup

Protocol and width converters (`projects/components/converters/`): the
AXI4↔AXIL4 and AXI4→APB4/APB5 protocol converters, the data-width
upsize/downsize primitives and the dwidth converter wrappers.

| State | Count |
|---|---|
| [open](open.md) | 2 |
| [closed](closed.md) | 4 |

## Open shortlist

*(CONV-007 closed 2026-08-25 same day: axi4_to_axil4_wr parked-burst-AW
W-path deadlock — w_burst_capture missing the awready qualifier; found
by the DV bridge parallel_storm, pinned by
test_pending_w_blocked_by_waiting_burst_aw.)*

- **CONV-006** — upsize paths require wide-aligned burst starts. Constraint
  now documented (MAS 2.5.5) and asserted in sim; lifting it (start-lane
  support in the width primitives) is scoped future work.

*(CONV-004 closed 2026-08-24: burst splitting on both dwidth paths;
run-all-full-parallel 112/112.)*


- **CONV-002** — mostly resolved: root cause was a doubled signal prefix
  (`wide_wide_data`), so data and LAST read 0 and every check failed. 7 of 9
  scenarios now asserted and green.
- **CONV-003** — CLOSED obsolete: the dual-buffer mode was deleted. Nothing
  instantiated it, it measured no faster than the single buffer, and it was
  the only configuration still failing.
- **CONV-001** — RESOLVED: the LAST mechanism is correct, proven by a
  deterministic test that holds wide_last low. The faults were all test-side.

## Replaying an intermittent

From the shared-scrub session, and worth keeping: these failures are
deterministic per **(RANDOM_SEED, compiled binary)**. Grep
`Seeding Python random module with N` from a failing run and replay with
`RANDOM_SEED=N`. The catch is that ANY rebuild -- including toggling
`WAVES=1` -- changes Verilator codegen and therefore which seeds fail, so a
`WAVES=1` run that "passes" has proved nothing. Under `pytest -n`, tests
launched in the same second share one seed, which is why a sweep can fail
several configs at once while solo loops run clean for hundreds of
iterations.
