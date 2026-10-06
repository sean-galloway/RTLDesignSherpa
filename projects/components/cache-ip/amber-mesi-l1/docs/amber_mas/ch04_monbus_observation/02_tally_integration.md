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

# Drop-and-Count Behavior and monbus_tally_axil

## Drop-and-Count Policy

`amber_monlite` is drop-and-count, not stall-and-backpressure. This preserves measurement integrity: the observer cannot perturb the cache hit/miss timing it is trying to measure.

When a packet is emitted and `mon_ready` is low, the packet is discarded and a saturating counter increments. When `mon_ready` next goes high, if the counter is non-zero an `AMBER_EV_DROPPED` packet is emitted with the count, and the counter clears.

## Counter Width

The drop counter is 8 bits. The probability of 256 consecutive drops in a correctly sized system is negligible; if it occurs, the counter saturates and the overflow is visible in the dropped packet.

## monbus_tally_axil Integration

Amber's MonBus connects to the shared `monbus_tally_axil` agent exactly like STREAM and every other component in the repo. The agent:

1. Accepts `mon_valid`/`mon_ready`.
2. Parses the 128-bit packet using `monitor_common_pkg`.
3. Maintains per-event-class counters in AXI-Lite addressable registers.
4. Reports dropped-packet counts.

## Software View

Software reads event counters through the `monbus_tally_axil` AXI-Lite slave. There is no APB CSR inside amber. The counter addresses and field layouts are defined by the tally agent, not by amber.

---

**Last Updated:** 2026-10-06
