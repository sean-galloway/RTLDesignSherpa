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

# Drain path selection

An interrupt answers, "What needs attention now?" A memory history answers,
"What happened, and in what order?" An SoC needs both questions answered, but
not necessarily for the same packet types.

The group has two sinks and a per-type steering mask
([monbus_group.md](../../rtl-amba/monitor/monbus_group.md)):

| Sink | Record | Reached by | Best for |
|---|---|---|---|
| **Error FIFO** | 192-bit `{timestamp, packet}`, read back as three 64-bit beats over the AXI-Lite slave; `irq_out` while non-empty | `cfg_<proto>_err_select[type] = 1` | the few packets a handler must act on now: errors, timeouts |
| **Write FIFO** | the same record as three beats (raw) or one beat (compressed), flushed as AXI bursts into the ring `[cfg_base_addr, cfg_limit_addr]` when `cfg_flush_watermark` beats are queued or the flush timeout elapses | everything not dropped and not selected for the error FIFO | bulk trace and memory-resident histories: errors, completions, latencies, thresholds |

The choice is per packet type per protocol, at runtime. The common shape is
errors and timeouts to the interrupt path and everything else to the trace
ring; a debug session flips completions over to the error FIFO for a while
and reads them one at a time.

For the opening incident, the integrator instead steers the error classes of
interest to the memory ring. The host sorts the records by event timestamp and
sees the bridge decode error first, then the DMA and stream timeouts, rather
than collecting fragments from three handlers. The raw ring remains in drain
order; its timestamps provide the chronological view. The ring is circular,
so its useful history is bounded by its size and by flush and loss policy; it
is not an infinite or inherently nonvolatile log. A system that needs it after
reset must preserve or capture the memory contents as part of its reset
architecture.

Steering selects a destination; it does not duplicate a packet into both
sinks. Urgent classes can therefore use the interrupt FIFO while archival
classes use memory. With multiple groups, each ring preserves its own
acceptance order, and the proposed global usync timestamps let software merge
the records into an SoC-wide event-time history.

> **Plane framing:** Drain-path selection is an output-plane decision:
> `monbus_group_core` steers each packet type to the interrupt/read FIFO or
> the master-write ring. The protocol and reporter planes only emit typed
> packets; they do not know which drain will consume them. See
> [Ocelus plane map](../../rtl-amba/monitor/monitor_planes.md).

![Drain paths: error FIFO with interrupt, write FIFO into the memory ring](../../assets/rtl-amba-monitors/graphviz/monitor_wp_drains.png)
