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

# Common Utilities

Shared helpers used by more than one block. Rule: a utility lives in HIVE's
`common/` only when the repo library has no equivalent; otherwise it is
imported, not copied.

| Module | Source | Used by | Notes |
|--------|--------|---------|-------|
| `gaxi_fifo_async` / AXIS async FIFO | repo GAXI library (`rtl/common`) | All CDC paths | Gray-pointer, house-verified; depths per §1.2 |
| `reset_synchronizer` | `rtl/cdc/` | Every domain | Pattern in §1.3 |
| `round_robin_arbiter` | repo common | `control_network` | Generic N-way; N=16 for the uplink |
| `credit_counter` | repo common (Delta-shared semantics) | Injection path | Credit accounting if Delta ingress requires it (confirm against Delta MAS) |
| `axis_fifo` (sync) | repo GAXI | Injection FIFOs | `serv_monitor` TX aperture |

: Utility inventory

Parameter consistency: `SERV_COUNT`, buffer depths, and FIFO widths come
from the single `hive_config.svh` include (Chapter 6); no block hardcodes
its own copy.

---

**Last Updated:** 2026-10-12
