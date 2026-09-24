# converters — task rollup

**Next ID: CONV-011** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`).
Pick the lane before filing:

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-001` |
| [bug/](bug/INDEX.md) | a defect with a reproduction | `BUG-001` |
| [issue/](issue/INDEX.md) | an anomaly/risk/question not yet diagnosed | `ISSUE-001` |

**The pages at this level are the LEGACY task lane.** They are frozen: close
them out where they stand, and do not add to them. New work of any kind goes in
a lane above. See [the convention](../../../INDEX.md) for the full definitions.


Protocol and width converters (`projects/components/converters/`): the
AXI4↔AXIL4 and AXI4→APB4/APB5 protocol converters, the data-width
upsize/downsize primitives and the dwidth converter wrappers.

| State | Count |
|---|---|
| [open](open.md) | 2 |
| [closed](closed.md) | 7 |

## Open shortlist

*(CONV-007 closed 2026-08-25 same day: axi4_to_axil4_wr parked-burst-AW
W-path deadlock — w_burst_capture missing the awready qualifier; found
by the DV bridge parallel_storm, pinned by
test_pending_w_blocked_by_waiting_burst_aw.)*

*(CONV-006 closed 2026-08-26: mid-wide-word INCR burst starts implemented
on both upsize paths — addressed-lane data + byte enables; FIXED/WRAP
stay wide-aligned, asserted.)*

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
