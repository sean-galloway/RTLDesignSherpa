# converters — task rollup

Protocol and width converters (`projects/components/converters/`): the
AXI4↔AXIL4 and AXI4→APB4/APB5 protocol converters, the data-width
upsize/downsize primitives and the dwidth converter wrappers.

| State | Count |
|---|---|
| [open](open.md) | 2 |
| [closed](closed.md) | 0 |

## Open shortlist

- **CONV-002** — the dnsize and upsize test files discard every scenario
  verdict, and all 22 configurations fail once asserted. Two width primitives
  with no working verification. P0.
- **CONV-001** — `test_burst_tracking` fails when its result is asserted, and
  has been discarding that result. Cause unresolved: either the TRACK_BURSTS
  LAST path is broken or the scenario mis-drives it.
