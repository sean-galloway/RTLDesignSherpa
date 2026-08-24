# converters — task rollup

Protocol and width converters (`projects/components/converters/`): the
AXI4↔AXIL4 and AXI4→APB4/APB5 protocol converters, the data-width
upsize/downsize primitives and the dwidth converter wrappers.

| State | Count |
|---|---|
| [open](open.md) | 1 |
| [closed](closed.md) | 2 |

## Open shortlist

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
