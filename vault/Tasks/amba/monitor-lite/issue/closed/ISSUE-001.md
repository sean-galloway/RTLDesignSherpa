# ISSUE-001: which monitored instances should switch to the lite

**Priority:** P3
**Status:** closed 2026-09-27 -- resolved into switches, every one made and measured (TASK-001 section 17)
**Owner:** TBD
**Related:** amba/monitor-lite TASK-001 (built and measured); amba ISSUE-001 (the monbus group's own timing chain, which the switch does not touch)

The lite exists as the `_monlite` sibling of every monitored wrapper and
per bridge (`mon_preset = "lite"`). Nothing has been switched. The candidates
and what each would give up:

- **STREAM / observers** (perf-first): gain nothing until the perf path is
  confirmed to live entirely in `axi_bus_meter`; the lite has no perf class
  by design. They also relied on `block_ready` to bound the table at 64
  slots; the lite gives drop-and-count instead, a behaviour change to state
  on the observers' page.
- **Generated bridges**: DECIDED 2026-09-26 (Sean) -- every monitored port
  in a generated bridge is the lite; the full monitor is no longer instantiated
  by the bridge generator. Only STREAM's in-core ports, the observers and the
  board-validation builds remain to decide.
- **Board monitor-validation builds**: coverage of the full monitor's
  classes is the point of those builds; not candidates.

**Resolves into:** a task per consumer that switches (naming the instance,
the preset and the test that proves the packets still arrive), or a recorded
no-action here for the ones that stay on the full monitor.

**Resolution (2026-09-27).** Every candidate switched, and the two doubts
above were answered by measurement:

- STREAM / observers: the perf path is confirmed to live entirely outside the
  monitor -- `axi_perf_latency_hist` is fed the raw AR/R handshakes and computes
  latency itself, `axi_bus_meter` classifies cycles, and the full monitor's own
  `perf_*` outputs were tied off in the observer and pruned. The `block_ready`
  table-bound is the lite's `refused_count` ("commands that found no free table
  entry"), the same condition counted instead of stalled, now sourcing
  `OBS_STICKY.TAP_BLOCKED`. Switched in 78cddb5e2; build-obs 184,047 -> 71,671
  LUTs; board packet counts per iteration unchanged on every class the lite
  emits; DUT meters bit-identical.
- STREAM in-core and RAPIDS beats: switched in 8cce2ecce, tested on silicon
  (build-mon 283-register walk and 7/7 monitor scenarios; RAPIDS golden-CRC
  smoke and 8-channel characterization).
- Board monitor-validation builds: build-mon and build-obs are those builds,
  and they are on the lite; the coverage they exist for is 5 of 7 packet
  classes, Perf and Debug being the two the lite does not emit, by design.

Nothing stays on the full monitor by choice. It remains available behind the
sixteen `_mon_cg` wrappers.
