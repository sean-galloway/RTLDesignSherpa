<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Packet-type filtering

Three layers, all runtime-programmable over the control APB:

1. **Type mask** at the group, `cfg_<proto>_pkt_mask[type]`: 1 drops the
   type. Also on every lite wrapper (`cfg_axi_pkt_mask`) so a dropped type
   never even leaves the port.
2. **Event mask** at the group, `cfg_<proto>_<class>_mask[event_code[3:0]]`:
   1 drops one event within a type, for example `RESP_SLVERR` but not
   `RESP_DECERR`.
3. **Enable pins** on the wrappers, `cfg_error_enable`, `cfg_compl_enable`,
   `cfg_timeout_enable`, `cfg_threshold_enable`: a class that is off is not
   generated at all, so it costs no monbus bandwidth.

**The congestion pitfall, and how the lite retires it.** On the full
monitor, completion and performance packets are the high-rate classes; with
both enabled on a busy port the monbus saturates and lower-priority packets
are lost silently. The rule from
[AXI_Monitor_Configuration_Guide.md](../../../user-guides/AXI_Monitor_Configuration_Guide.md)
stands there: never enable `cfg_compl_enable` and `cfg_perf_enable`
together. The lite has no performance class to collide with, holds a
timeout or a latency event that loses the pick until it can go, and when
its queue is genuinely full it counts the loss and reports the count in one
`Error/EVENT_DROPPED` packet as soon as the bus is free. Nothing is lost
silently; the consumer always knows how many events it did not see, which
is the property a filtering strategy can be built on.

![Packet-type filtering: enable pins, type mask, event mask, then drain steering; the lite counts what its queue could not take](../../assets/rtl-amba/monitor_wp_filtering.png)
