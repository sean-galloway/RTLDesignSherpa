# The MonBus is a low-bandwidth event channel; one knob setting floods it

**Rule:** ocelus and the MonBus behind it carry RARE, MEANINGFUL events:
errors, timeouts, threshold crossings, a sampled completion, a drop report.
The channel is sized for that and nothing more. A reporter publishes at most
one packet per two cycles; a group's AXI-Lite writer spends several cycles a
packet word; the arbiter in front of a tally shares that with every observer
on the chain. Every per-transaction class the monitors can emit (completions,
perf, debug trace, a transaction-start, a gather) is a knob that exceeds the
channel the moment traffic is sustained. The knobs are there so ONE monitor
serves both a functional-debug configuration and a performance one. Turning
them all on is not maximum observability; it is a flood, and a flooded
channel's counts are lower bounds with no indication of how low.

The design follows from the intent, so it is not a defect to fix: the packet
masks reset to drop; a reporter holds rather than overruns; an observer that
cannot keep up loses observations and says so ([[observers-do-not-drive]]);
fixed priority lets an error stream starve trace, because errors matter more
than throughput. None of that is to be "raised" so that a per-transaction
stream fits.

## How to apply

- **Pick a class set per run, never the union.** Functional debug is error +
  completion + timeout; performance is error + perf with completions off;
  debug trace goes on alone. `rtl/amba/CLAUDE.md` Rule #1 is this rule stated
  at the instantiation.
- **Budget the emission against the drain.** Aggregate emission at 50 to 80
  percent of what the chain drains, watched through the group's
  `trace_overflow` flag and the always-on bus meters; the stream-mon
  [[testplan]] gives the tuning loop ("busy, not flooded").
- **A host program does not open the mask to see everything.** The masks
  reset to drop for a reason ([[new-monbus-protocol]]); a program that admits
  every type admits the per-beat perf stream.
- **Filter by content, not only by class.** A class mask turns a class on
  or off; it does not make a per-transaction class low-bandwidth. The AXI
  monitors carry the other half of the idiom for exactly this reason: the
  address-range and ID filters (`axi_monitor_lite` `cfg_addr_range_enable`
  / `cfg_addr_match_enable`, `axi_monitor_filtered` `ADDR_FILTER_ENABLE` /
  `ID_FILTER_ENABLE`). A monitor that emitted on every read and write would
  flood the channel too; the filters make the stream a watch on a window
  (these lines, this requester) rather than everything, and the window's
  event rate is what the channel is sized for. An observer on a new block
  gets the class layers AND a content filter keyed on what that block
  attributes events to (an address window, a port, a slot). Owner,
  2026-11-22.
- **A number that must be exact under load is a counter, not a packet
  stream.** Put the counter beside the observer, snapshot both in one frozen
  window, and read the tally bins as lower bounds on the board. The observer
  keeps its job: shape in time, payload, latency, the rare event.
- **An observer with no class knob emits everything.** Wherever its event rate
  is per transaction that is a flood by construction. Give it the same
  per-class mask the monitors carry, reset to the rare classes, and the
  content filter above; the mask alone still floods in thrash (onyx on the
  reference rig: one class alone fits at injector depth 1 and 2 and loses a
  fifth of its events at depth 8, because the class fires on every
  transaction and nothing narrows which).
- **A drop report is itself low-bandwidth.** The drop-and-count idiom emits
  when nothing is waiting and carries a small saturating count; under a
  sustained flood it says "lost", not "how many". Do not read the lost count
  as a count.

## The failures that taught it

| when | where | what happened |
|---|---|---|
| 2025 | `rtl/amba` monitors | completion and perf enabled together under heavy traffic congested the bus; became Rule #1 of the area |
| 2026-09-08 | STREAM Genesys 2, five host programs | one program's mask allowed every type, admitting the ~1.1M-packet perf stream; the group flooded and the UART wedged; the board read as broken for a day ([[uart-harness]]) |
| 2026-09 | stream-mon coverage campaign | the sequences had to be split so no run enables everything; the drain rate of about one packet per two cycles set the "busy, not flooded" budget ([[testplan]]) |
| 2026-11-22 | onyx on the Genesys 2 reference rig | the coherency unit's observer emits four per-transaction classes with no mask; in every thrash cell its holders overflowed for the whole run while its six counters stayed exact (bin 11 read 12,613 against 20,240 transactions). Filed as onyx ISSUE-001, which this note reframes: the channel did what it is for; the observer lacked the knob. Fixed the same day: `onyx_monlite` carries the ocelus layers (observer, packet type, event class, error code, port), reset to the rare class only |

What the onyx case adds: the sim held the observer to its model and lost 0 to
9 events a cell, every one reported, which looked like a channel with margin.
The board's chain, shared by three observers and crossing an AXI-Lite hop,
has a drain rate the sim never exercised. The counters, not the bins, carried
the measurement, and the handbook now says so before the next design puts a
per-transaction class on the channel and reads the bins as counts.

Related: [[observers-do-not-drive]], [[new-monbus-protocol]], [[sizing-invariants]], [[monitor-board-coverage]].
