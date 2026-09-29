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

# The spine

Every monitored port emits 128-bit packets onto a monitor bus (monbus). An
arbiter tree merges the ports of a block into one stream, and a monbus group
sinks that stream into two paths: an error FIFO the host reads over
AXI-Lite behind an interrupt, and a write FIFO the group flushes as AXI
bursts into a memory ring. Filtering happens at the group, per protocol and
per packet type. The packet layout is fixed
([monitor_package_spec.md](../../rtl-amba/includes/monitor_package_spec.md)); everything
else on this page is a knob.

![Monitor system spine: ports, arbiter tree, group, two drains](../../assets/rtl-amba/monitor_wp_spine.png)
