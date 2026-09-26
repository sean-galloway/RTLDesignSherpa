# ISSUE-001: which monitored instances should switch to the lite

**Priority:** P3
**Status:** open
**Owner:** TBD
**Related:** amba/monitor-lite TASK-001 (built and measured); amba ISSUE-001 (the monbus group's own timing chain, which the switch does not touch)

The lite exists and is selectable per wrapper instance (`MONITOR_LITE=1`) and
per bridge (`mon_preset = "lite"`). Nothing has been switched. The candidates
and what each would give up:

- **STREAM / observers** (perf-first): gain nothing until the perf path is
  confirmed to live entirely in `axi_bus_meter`; the lite has no perf class
  by design. They also relied on `block_ready` to bound the table at 64
  slots; the lite gives drop-and-count instead, a behaviour change to state
  on the observers' page.
- **Bridge fixtures with `error_only`**: the lite emits the same four
  classes the preset keeps; the only loss is the address-range checker and
  the ID/latency filters.
- **Board monitor-validation builds**: coverage of the full monitor's
  classes is the point of those builds; not candidates.

**Resolves into:** a task per consumer that switches (naming the instance,
the preset and the test that proves the packets still arrive), or a recorded
no-action here for the ones that stay on the full monitor.
