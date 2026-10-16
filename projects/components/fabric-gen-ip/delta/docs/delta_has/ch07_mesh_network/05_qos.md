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

# Quality of Service

## Three Traffic Classes

> **IMPLEMENTED** — QoS arbitration is built into `delta_mesh_cell`. The design is per the delta mesh design spec dated 2026-10-13 (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`).

Delta's mesh defines 3 QoS classes:

- **Class 0 — config/control** — highest priority; must never be blocked by data traffic.
- **Class 1 — latency** — interactive or latency-sensitive traffic.
- **Class 2 — bulk** — throughput traffic that can tolerate delay.

This split mirrors the control/data-plane priority split common in NPU practice.

## Strict Priority With Aging

Every output port uses strict priority among the classes. To prevent starvation of lower-priority traffic, the arbiter includes programmable aging: a lower-priority request that has waited too long is temporarily promoted above a newer higher-priority request.

Aging alone is not enough for class 2 under heavy class-0/1 load. A bulk minimum reservation guarantees that some fraction of each cycle is spent serving bulk traffic.

## Non-Interference

Each class has separate VCs and separate injection buffers. Shared buffers let tree-saturation traffic in one class block unrelated traffic even with priority bits, so delta keeps the resources separate. Config class traffic gets its own VC0 slice so control can never be bulk-blocked.

## Per-Class Routes

The routing table is keyed by `(destination, QoS class)`, so each class can follow an independent route to the same destination. Latency class might take a low-contention path while bulk class takes the shortest physical path.

## Within-Class Fairness

Per-flow weighted round-robin or deficit round-robin within a class is a known enhancement. It is deferred until a user needs it; the current design provides class isolation and class-level fairness only.
