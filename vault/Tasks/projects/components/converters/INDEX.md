# converters — task rollup

Protocol and width converters (`projects/components/converters/`): the
AXI4↔AXIL4 and AXI4→APB4/APB5 protocol converters, the data-width
upsize/downsize primitives and the dwidth converter wrappers.

| State | Count |
|---|---|
| [open](open.md) | 2 |
| [closed](closed.md) | 0 |

## Open shortlist

- **CONV-002** — mostly resolved: root cause was a doubled signal prefix
  (`wide_wide_data`), so data and LAST read 0 and every check failed. 7 of 9
  scenarios now asserted and green.
- **CONV-003** — dnsize DUAL buffer: dropped beats AND misplaced LAST, across
  three scenarios including a simple (non-burst-tracking) config. Single
  buffer is clean. Intermittent. Needs a deterministic reproducer. P1.
- **CONV-001** — RESOLVED: the LAST mechanism is correct, proven by a
  deterministic test that holds wide_last low. The faults were all test-side.
