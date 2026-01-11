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

# Interface Overview

**Last Updated:** 2025-01-10

---

## External Interfaces

The RAPIDS Beats architecture exposes the following external interfaces:

### AXI4 Master Interfaces

| Interface | Purpose | Data Width |
|-----------|---------|------------|
| Descriptor AXI | Fetch descriptors from memory | 256-bit |
| Sink AXI Write | Write sink data to memory | 512-bit (param) |
| Source AXI Read | Read source data from memory | 512-bit (param) |

: Table 4.0.1: AXI4 Master Interfaces

### Streaming Interfaces

| Interface | Type | Purpose |
|-----------|------|---------|
| Fill Interface | Custom | Network data ingress (to SRAM) |
| Drain Interface | Custom | Network data egress (from SRAM) |
| AXIS Sink | AXI-Stream Slave | Optional AXIS wrapper for fill |
| AXIS Source | AXI-Stream Master | Optional AXIS wrapper for drain |

: Table 4.0.2: Streaming Interfaces

### Control/Monitor Interfaces

| Interface | Type | Purpose |
|-----------|------|---------|
| APB | APB slave | Per-channel kick-off |
| Configuration | Custom | Global/per-channel config |
| Status | Custom | Idle, state, error flags |
| MonBus | Custom 64-bit | Monitor packet output |

: Table 4.0.3: Control and Monitor Interfaces

---

## Interface Documentation

- [AXI4 Interface Specification](01_axi4_interface_spec.md) - Descriptor, sink write, source read
- [AXIS Interface Specification](02_axis_interface_spec.md) - Optional streaming wrappers
- [MonBus Interface Specification](03_monbus_interface_spec.md) - Monitor packet format

---

## Interface Signal Naming Conventions

| Prefix | Meaning | Example |
|--------|---------|---------|
| `m_axi_` | AXI master port | `m_axi_arvalid` |
| `s_axi_` | AXI slave port | `s_axi_awready` |
| `m_axis_` | AXIS master port | `m_axis_tvalid` |
| `s_axis_` | AXIS slave port | `s_axis_tready` |
| `cfg_` | Configuration input | `cfg_enable` |
| `snk_` | Sink data path | `snk_fill_valid` |
| `src_` | Source data path | `src_drain_ready` |
| `sched_` | Scheduler interface | `sched_rd_valid` |
| `monbus_` | Monitor bus | `monbus_pkt_data` |

: Table 4.0.4: Signal Naming Conventions

---

**Last Updated:** 2025-01-10
