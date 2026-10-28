# Overview: from an SoC failure to a usable history

An SoC failure usually arrives as a sequence, not as one isolated error. A
malformed descriptor sends a DMA transaction to an unmapped address. The
bridge rejects it. The DMA later times out waiting for completion, and the
stream waiting for that data times out in turn. Every monitor has seen
something real, but three disconnected alarms leave software to guess which
event came first and which are consequences.

Now give those events a common microsecond time base and collect the error
records in a reserved memory region:

| Time (µs) | Source | Event |
|---:|---|---|
| 18,442,731 | AXI bridge | Address decode error |
| 18,442,935 | DMA channel 2 | Completion timeout |
| 18,443,002 | Output stream | Data timeout |

The list does not prove causality by itself. It does something immediately
useful: it puts the earliest observed fault in front of the engineer, preserves
the sequence that followed, and associates each record with its source. The
investigation starts with the bridge and the descriptor instead of with three
unrelated interrupt handlers. A history in memory is also available for
postmortem capture when no live host can service each event as it arrives.

That is the SoC-level purpose of Ocelus. The monitors, timestamps, identities,
aggregation tree, and drains are not ends in themselves; together they turn
distributed symptoms into evidence software can read in context.

Ocelus — from the Latin *ocellus*, "little eye"; a bee's simple always-on
eye — is the repository's monitor fabric: the blocks, the packet format, and
the drain machinery that watch a design while it runs and report what
crosses the conditions you set. It is **not limited to tracking simple
interfaces**, however the earlier drafts of this paper read. The port
monitors are its most visible producers, but the fabric equally carries:

- **Protocol events** from passive taps on any handshake: AXI4/AXI5,
  AXI-Lite, AXI-Stream, CXS, APB, Wishbone — full and lite monitors per
  port family.
- **In-core events** from blocks that emit their own: STREAM's descriptor
  engine and scheduler carry lite monitors *inside* the DMA core; RAPIDS
  monitors its descriptor and AXIS interfaces the same way; the bridge
  generator puts one on every monitored port.
- **In-datapath measurement** that needs no transaction tracking at all:
  the `axi_bus_meter` counts beats, bytes and idles in the flow, and the
  pass-through observer watches a mid-fabric link with its own
  configuration.
- **Error, debug and performance classes** as first-class packet types with
  their own reporters, not as afterthoughts of a protocol trace.

## The five planes

The fabric is sliced into five purpose planes. Each is a unit you can keep
or drop at build time; dropping one never reroutes the others. Where you
see `plane` in a name anywhere in this repository, this is the discipline
it refers to.

| Plane | Job | Representative members |
|---|---|---|
| **Protocol** | Observe the bus, packetize protocol events | `axi_monitor_lite`, `axi_monitor_base`, `axis_monitor_lite`, `cxs_monitor_lite`, the transaction manager/CAM/timeout/addr-check blocks |
| **Error** | Detect and packetize errors, timeouts, threshold crossings | `axi_monitor_reporter_error`, `..._timeout`, `..._threshold` |
| **Debug** | Completion and debug-trace packets | `axi_monitor_reporter_debug`, `..._compl` |
| **Perf** | Roll counters up into performance packets | `axi_monitor_reporter_perf`, in-datapath `axi_bus_meter` |
| **Output** | Arbitrate, filter, compress, drain packets to the host or memory | `monbus_arbiter` tree, `monbus_group_*` family, compressor, halfbeat packer, capture CAMs |

The contract between planes is fixed and small: the protocol plane taps the
bus passively and never drives it back; the error, debug and perf planes
each consume only the events they own; every plane emits the same typed
128-bit `monitor_packet_t` with a 64-bit timestamp; and the output plane
merges everything onto one monbus and drains it — an interrupt-backed error
FIFO the host reads over AXI-Lite, and a write FIFO flushed as AXI bursts
into a memory ring. The full membership table and the build personas
(bring-up, silicon-perf, field-debug, full) live in the
[Ocelus plane map](../../rtl-amba/monitor/monitor_planes.md).

## An implementation, end to end

The figure below is a real one — the three-port AXI4 read bridge fixture
the cost numbers in [chapter 10](10_what_it_costs.md) come from, monitored
the way the bridge generator monitors every build: one lite monitor per
slave port, a round-robin arbiter tree, one shared group, two drains. The
whole monitored bridge costs about 5,300 LUTs against 826 unmonitored, and
meets timing on both boards with margin to spare.

![A monitored three-port read bridge: per-port lite monitors, arbiter tree, group, error and trace drains](../../assets/rtl-amba-monitors/graphviz/monitor_wp_implementation.png)

Three flows, traceable at a glance: the **observed traffic** crosses the
top on the bridge's own AXI path — the monitors tap it passively (dashed)
and never touch it. The **monitor packets** flow top-down the center from
each tap through the arbiter tree into the group, which filters by packet
type and steers by class. The **drains** leave through the boundary bar at
the bottom: error-class records to the interrupt-backed FIFO the host reads
over AXI-Lite, everything else as AXI bursts into the memory ring. The
configuration APB enters the group from the side; it owns every mask and
threshold named in the following chapters.

## What the integrator owns

Everything on the figure that is not fixed by the packet format is a knob,
and each knob has a chapter:

| Axis | Chapter |
|---|---|
| The spine itself: ports, tree, group, two drains | [2](02_the_spine.md) |
| Which monitor: the lite, unless you can say why not | [3](03_which_monitor.md) |
| Identity space allocation (`unit_id` / `agent_id`) | [4](04_identity_space_allocation.md) |
| Where to insert monitoring (port, mid-fabric, root) | [5](05_where_to_insert_monitoring.md) |
| Timestamp policy | [6](06_timestamp_policy.md) |
| Drain path selection | [7](07_drain_path_selection.md) |
| Packet-type filtering | [8](08_packet_type_filtering.md) |
| Aggregation topology | [9](09_aggregation_topology.md) |
| What it costs | [10](10_what_it_costs.md) |
| Validating a tweak in simulation | [11](11_validating_a_tweak_in_simulation.md) |
| Relationship to Nexus (IEEE-ISTO 5001) | [13](13_relationship_to_nexus.md) |

All citations are collected in the [references](14_references.md) chapter
at the end.
