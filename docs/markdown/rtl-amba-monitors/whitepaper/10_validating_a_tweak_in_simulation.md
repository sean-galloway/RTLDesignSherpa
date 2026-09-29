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

# Validating a tweak in simulation

Three templates in the tree exercise exactly the knobs above:

- `val/amba/test_axi_mon_block_ready.py`: saturate a port and prove the
  monitor's admission contract, `block_ready` on the full monitor and the
  refuse-count identity on the lite.
- `val/amba/test_axi_monitor_soak.py::monitor_soak_monlite`: random traffic
  with backpressure, asserting that every generated event is delivered or
  counted as dropped. Change a mask or a drain and this is the identity that
  must still close.
- `formal/amba/monbus_group_core`: the routing rule, `monbus_ready`, the FIFO
  accounting and the legality of the flush burst, proved at the ports. A
  change to the group's filtering or drain logic re-runs against it.

The error-injection template the original outline named
(`test_bridge_1x2_rd_monitor_error_inject.py`) is not in the tree; the
bridge's generated monitor stress tests cover that ground.
