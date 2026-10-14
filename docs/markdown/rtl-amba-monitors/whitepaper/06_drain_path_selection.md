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

The group has two sinks and a per-type steering mask
([monbus_group.md](../../rtl-amba/monitor/monbus_group.md)):

| Sink | Record | Reached by | Best for |
|---|---|---|---|
| **Error FIFO** | 192-bit `{timestamp, packet}`, read back as three 64-bit beats over the AXI-Lite slave; `irq_out` while non-empty | `cfg_<proto>_err_select[type] = 1` | the few packets a handler must act on now: errors, timeouts |
| **Write FIFO** | the same record as three beats (raw) or one beat (compressed), flushed as AXI bursts into the ring `[cfg_base_addr, cfg_limit_addr]` when `cfg_flush_watermark` beats are queued or the flush timeout elapses | everything not dropped and not selected for the error FIFO | bulk trace: completions, latencies, thresholds, for offline analysis |

The choice is per packet type per protocol, at runtime. The common shape is
errors and timeouts to the interrupt path and everything else to the trace
ring; a debug session flips completions over to the error FIFO for a while
and reads them one at a time.

![Drain paths: error FIFO with interrupt, write FIFO into the memory ring](../../assets/rtl-amba-monitors/graphviz/monitor_wp_drains.png)

## References

The Ocelus is an original design of this repository. The papers and standards below are related work for comparison, not sources of the design; protocol specifications define the rules the monitor observes.

- Hopkins, A.B.T., McDonald-Maier, K.D. "Debug Support for Complex Systems On-Chip: A Review." *IEE Proc. Computers and Digital Techniques*, 153(4):197-207, 2006. DOI: [10.1049/ip-cdt:20050194](https://doi.org/10.1049/ip-cdt:20050194). -- related work: on-chip trace buffers versus trace ports.
- Yang, F.-C., Lin, Y., Kao, C.-F., Huang, I.-J. "An On-Chip AHB Bus Tracer With Real-Time Compression and Dynamic Multiresolution Supports for SoC." *IEEE Trans. VLSI Systems*, 19(4):571-584, Apr. 2011. DOI: [10.1109/TVLSI.2009.2039811](https://doi.org/10.1109/TVLSI.2009.2039811). -- related work: a bus tracer recording into an on-chip circular buffer.
- Indexed in `rtl/amba/references/README.md` (Monitor subsystem family; citation only)
