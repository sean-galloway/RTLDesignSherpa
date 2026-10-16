# A new monbus protocol is not done until every consumer passes it

**Rule:** a new `PROTOCOL_*` value has to be added everywhere monbus packets
are consumed, not only where they are produced: the monitor that emits it,
the Python decoder (`bin/TBClasses/monbus`), AND every filter between the two,
which in practice means `rtl/amba/ocelus/monbus_group_core.sv`. That filter's
`case (pkt_protocol)` ends in `default: pkt_drop = 1'b1`, so a protocol it has
not been told about is consumed and discarded. Nothing errors, nothing gets
counted, and the packet is simply gone.

## The failure that taught it

CXS (2026-10-15) got `PROTOCOL_CXS = 4'h6`, `cxs_monitor_lite`, the Python
decode and passing monitor-lite tests. All of those tests read the monitor's
own monbus port directly. The first design to send CXS packets through a monbus
group (the RAPIDS CXS planes) captured zero of them. The group had been
dropping every CXS packet at its filter. The datapath scoreboards passed the
whole time. Only a test that counted completions at the capture master's
memory exposed it.

## How to apply

- When you add a protocol, grep for `case (pkt_protocol)` and for every
  `PROTOCOL_` enumeration in the RTL and the formal reference models
  (`formal/amba/monbus_group_core/`), and give the new value a decision in each one.
- A stream-shaped protocol can share an existing mask slot instead of adding
  ports to every group wrapper. CXS uses the AXIS slot because its packet types
  are the same set.
- At least one test must take the new packets end to end through a group to
  the capture. A test that taps the monitor port proves the monitor and nothing
  downstream of it.

Related: [[observers-do-not-drive]], [[generated-rtl-discipline]].
