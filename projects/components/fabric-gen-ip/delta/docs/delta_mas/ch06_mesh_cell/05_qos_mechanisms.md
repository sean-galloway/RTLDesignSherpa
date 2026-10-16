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

# QoS Mechanisms

> **IMPLEMENTED:** This chapter describes the `delta_mesh_cell` QoS mechanisms as built. The design is per the 2026-10-13 design spec (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`).

Delta defines three QoS classes with strict priority at every output port. The split follows the control/data-plane separation common in NPU practice: class 0 for config, class 1 for latency traffic, class 2 for bulk [Q4][Q5].

| Class | Name | Priority | Typical use |
|---|---|---|---|
| 0 | Config / control | Highest | In-band table loads, mode switches, rapids control |
| 1 | Latency | Middle | Compute traffic with deadline requirements |
| 2 | Bulk | Lowest | Background data movement |

: QoS class mapping

## Strict Priority and Programmable Aging

The arbiter uses strict priority by default: a class-0 request always wins over class 1 and 2. To prevent indefinite starvation of lower classes, each class has a programmable aging counter. After the counter expires, the effective priority inverts so the lower class gets service [D13]. The counter is per-output-port and reloads automatically.

## Bulk Minimum Reservation

Aging alone is not enough. Under sustained latency traffic, bulk could still be starved because every fresh class-1 request would preempt the aged class-2 grant. The cell therefore maintains a bulk minimum reservation counter: after a programmable number of consecutive higher-priority grants, the next grant is forced to class 2 regardless of pending higher-priority requests [D1][Q5]. This guarantees a floor of bulk bandwidth without relying on traffic patterns.

## Class Non-Interference

Priority bits are insufficient when traffic classes share buffers. Tree-saturation in one class can block unrelated traffic through a shared input buffer even if that traffic has a priority bit [P14: §15.5]. Delta avoids this by giving each class its own VC *and* its own injection buffer at the local port. Config traffic rides a dedicated slice of VC0 so control can never be bulk-blocked.

| Isolation mechanism | Where applied |
|---|---|
| Separate VCs per class | Every input port |
| Separate injection buffers per class | Local port only |
| Independent table region per class | Per-destination route diversity |

: Class isolation resources

## Failure Mode: Aging Inversion Misconfiguration

If the aging counter is set too large, class 2 starves. If it is set too small, class 1 loses its latency advantage. The verification suite sweeps the counter and checks that bulk gets at least its reserved fraction under a tree-saturation attack.

## References

- Duato, Yalamanchili, Ni, *Interconnection Networks: An Engineering Approach*, 2nd ed., Morgan Kaufmann, 2003 — starvation under priority and bulk reservation need [D1][D13].
- Dally & Towles, *Principles and Practices of Interconnection Networks*, Morgan Kaufmann, 2004 — separation of resources to avoid tree saturation [P14].
- Franklin et al. (eds.), *Network Processor Design: Issues and Practices, Vol. 1*, Morgan Kaufmann, 2002 — NPU QoS practice and ASPEN scheduler starvation prevention [Q4][Q5].
