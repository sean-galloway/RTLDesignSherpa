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

# Aggregation topology

| Topology | Block | When |
|---|---|---|
| **Tree of round-robin arbiters** (default) | `monbus_arbiter`, any fan-in, ACK-mode grants | ports of similar rate; simplest, fair |
| **Weighted** | `arbiter_wrr_pwm_monbus` (weights per client, PWM flow control); `arbiter_rr_pwm_monbus` is the unweighted sibling | one port far busier than the others and you want its packets to win proportionally, not equally |
| **Protocol-partitioned groups** | one `monbus_group_core` per protocol family instead of the shared AXI / AXIS / CORE slots | the families need different rings, different interrupt handlers, or different flush policies |

The group core is shared by every wrapper family (AXI4, AXI5, AXI-Lite,
AXIS, Wishbone), so partitioning is a topology decision, not a new block.

![Aggregation topologies: round-robin tree, weighted, protocol-partitioned](../../assets/rtl-amba/monitor_wp_aggregation.png)
