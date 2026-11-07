<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/fpga-systems/NexysA7/misc-ip/cdc_counter_display — task rollup

Canonical tracker for the Nexys A7 CDC counter display demo
(`projects/fpga-systems/NexysA7/misc-ip/cdc_counter_display/`): `build-demo`
(`cdc_demo_top`, four counters, five runtime CDC modes, UART harness),
`build-phase1` (the original button-only top), and their docs, books and
episode scripts. The CDC primitives themselves are tracked in
[rtl/cdc](../../../../../rtl/cdc/INDEX.md).

Created 2026-11-07, when `docs/CDC_DEMO_TODO.md` was folded in: its build plan
closed as TASK-001, the parts never built became TASK-002 to TASK-005, and its
background sections became `docs/CDC_FAILURE_MODES.md` beside the demo.

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state. Moving an item between states is `git mv`. Each lane carries its own
`Next ID`.

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 4 | 0 | 1 | 0 | 0 |
| [bug/](bug/INDEX.md) | 0 | 0 | 0 | 0 | 0 |
| [issue/](issue/INDEX.md) | 0 | 0 | 0 | 0 | 0 |

Open counts exclude the reserved `-000` template in each lane.

Cite an item from outside with the area: "cdc_counter_display TASK-002".
