# converters — task rollup

Protocol and width converters (`projects/components/converters/`): the
AXI4↔AXIL4 and AXI4→APB4/APB5 protocol converters, the data-width
upsize/downsize primitives and the dwidth converter wrappers.

| State | Count |
|---|---|
| [open](open.md) | 3 |
| [closed](closed.md) | 0 |

## Open shortlist

- **CONV-002** — mostly resolved: root cause was a doubled signal prefix
  (`wide_wide_data`), so data and LAST read 0 and every check failed. 7 of 9
  scenarios now asserted and green.
- **CONV-003** — dnsize DUAL buffer loses 4 of 40 beats under backpressure;
  the tail is polled, so they are dropped rather than late. P1.
- **CONV-001** — `test_burst_tracking` fails when its result is asserted, and
  has been discarding that result. Cause unresolved: either the TRACK_BURSTS
  LAST path is broken or the scenario mis-drives it.
