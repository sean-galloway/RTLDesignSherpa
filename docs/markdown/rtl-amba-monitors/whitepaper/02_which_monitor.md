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

# Which monitor: the lite, unless you can say why not

Two monitors implement the port end of the spine. `axi_monitor_base`, the
full monitor, tracks transactions in a CAM and drives six reporter cones
(error, timeout, completion, threshold, performance, debug) with ID and
address filtering. `axi_monitor_lite` tracks the same transactions in
per-ID linked lists, emits errors, timeouts, completions with latency,
thresholds and address-range events, and drops the performance and debug
classes and the ID filter. Measured at their default parameters, out of
context, on the Kintex-7 the boards ship on
([monitor/monitor_characterization.md](../../rtl-amba/monitor/monitor_characterization.md)):

| | Full monitor | Lite | Ratio |
|---|---:|---:|---:|
| AXI4 read monitor, LUTs | 7,006 | 1,115 | 6.3x |
| AXI4 read monitor, flops | 5,219 | 1,027 | 5.1x |
| AXI-Lite read monitor, LUTs | 2,891 | 929 | 3.1x |
| 6.667 ns on Kintex-7 325T -2, register to register | misses (CAM at 16 slots) | meets, 0.8 to 1.5 ns spare | |
| 10 ns on Artix-7 100T -1 | misses by 1.45 ns | meets by 0.6 ns | |

That is why the lite is the default: the bridge generator instantiates it on
every monitored port, STREAM's three in-core monitors and RAPIDS' descriptor
and AXIS monitors are lite, and every board build since 2026-09-26 carries
it. It is also the more honest of the two under load. A full monitor that
runs out of table entries stalls the command channel (`block_ready`); the
lite never stalls the bus, counts the command it could not track
(`refused_count`), and when its output queue is full it counts the events
it could not deliver and reports the count in one `Error/EVENT_DROPPED`
packet as soon as the bus is free. Its contract is exact and is proved in
the tree: every command is completed, refused or live, and every generated
event is delivered, reported dropped or pending, with no fourth outcome
(`val/amba/test_axi_mon_block_ready.py`, `test_axi_monitor_soak.py`,
`formal/amba/axi_monitor_lite`). A stalled bus is the one effect an
instrument must never have on the design it watches.

What you give up, and when it matters:

| Full-monitor feature | Lite | Reach for the full monitor if |
|---|---|---|
| performance windows (`cfg_perf_enable`, byte/beat/idle counters) | none; the in-datapath `axi_bus_meter` and the pass-through observer measure throughput without a monitor | you need windowed bandwidth numbers from the monitor itself |
| debug trace packets | none | you need per-beat trace, not events |
| ID-range filter (`ID_FILTER_ENABLE`) | none; one lite per port, sliced by `unit_id`/`agent_id` instead | several instances must share one port by ID |
| 16 slots | 8 by default, parameter | more than eight transactions in flight per port and every one must be tracked, not counted as refused |
| address filter | address ranges kept (`N_ADDR_RANGES`, error or match per range) | |

The rest of this paper assumes the lite at the ports. Every axis below is
the same for both monitors; the numbers are the lite's.
