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

- When you add a protocol, give it a line in `ocelus_common_pkg::filter_family()`
  (and its mirror in `formal/amba/monbus_group_core/` and `TBClasses.monbus`)
  if its packet-type set is not the AXI family's; an unnamed value already
  takes the AXI masks and is seen. Then grep for `PROTOCOL_` in every
  consumer anyway: a decoder name table or a tally still needs the value.
- A stream-shaped protocol can share an existing mask slot instead of adding
  ports to every group wrapper. CXS uses the AXIS slot because its packet types
  are the same set.
- At least one test must take the new packets end to end through a group to
  the capture. A test that taps the monitor port proves the monitor and nothing
  downstream of it.

- Closed 2026-10-30 (owner: "fix all of it so new packet types can be seen
  at all"): the filter in both group cores and the formal model is now
  `case (filter_family(pkt_protocol))` with NO hard-drop default.
  `ocelus_common_pkg::filter_family()` is the one source, mirrored by
  `TBClasses.monbus.filter_family` with a parity test. APB, ARB, WB and CHI
  had all been dropped at every group; the 1wr test now sends every one of
  the sixteen protocol values through to the capture. Dropping most classes
  by DEFAULT stays the design (mask registers reset to drop so an all-on
  system cannot flood itself), but a mask is configurable and the hard
  drop was not.

Related: [[observers-do-not-drive]], [[generated-rtl-discipline]], [[transaction-monitor-keys]].
