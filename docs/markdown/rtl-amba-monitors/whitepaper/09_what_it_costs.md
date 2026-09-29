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

# What it costs

Standalone, at default parameters, from the characterization sweep
([monitor/monitor_characterization.md](../../rtl-amba/monitor/monitor_characterization.md)),
and in place, from the bridge fixture with the bridge's parameters
([axi_monitor_lite.md](../../rtl-amba/monitor/axi_monitor_lite.md)):

| | Full monitor | Lite |
|---|---:|---:|
| One AXI4 read monitor at defaults (16 / 8 slots), LUTs / FFs | 7,006 / 5,219 | 1,115 / 1,027 |
| One read monitor in the bridge, LUTs / FFs | 3,249 / 1,628 | 677 / 831 |
| Three-port read bridge with group, LUTs | 12,625 | 5,339 |
| The unmonitored bridge, LUTs | 826 | 826 |
| Kintex-7 325T -2 at 6.667 ns, bridge WNS | +0.212 ns | +1.092 ns |
| Kintex-7 at 6.667 ns, standalone at defaults, register to register | -0.166 ns | +1.005 ns |
| A group (error FIFO 64 records, write FIFO 96 beats), LUTs / FFs | 1,700 to 2,000 / 1,150 to 1,390 | same, shared |

The lite bridge fixture meets 10 ns on the Artix-7 100T -1 since 2026-09-28
(+0.366 ns), after the group planner and the lite's event stage were
re-pipelined (amba ISSUE-001, monitor-lite ISSUE-002). The per-variant
characterization -- every wrapper family, with and without clock gating,
full against lite, on both parts, from one repeatable flow -- is
[monitor/monitor_characterization.md](../../rtl-amba/monitor/monitor_characterization.md).
Its headline: at default parameters the full AXI monitor is about 7,000
LUTs and the lite about 1,100, and the lite meets 150 MHz on the Kintex-7
with 0.8 ns or more to spare where the 16-slot full monitor does not.
