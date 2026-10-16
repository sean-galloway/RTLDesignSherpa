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

# Interface Summary

## External Interface Overview

RAPIDS Beats exposes the following external interfaces. The network side is
a swappable plane: the AXIS tops (`rapids_beats_top`, `rapids_top`) carry the
`s_axis_*` / `m_axis_*` streams, and the CXS tops (`rapids_beats_cxs_top`,
`rapids_cxs_top`) carry one CXS link per direction in their place (see the CXS
Network Interface chapter). Everything else is identical.

### Figure 3.1.1: External Interfaces

![External Interfaces](../assets/graphviz/ch01_system_integration.png)

**Source:** [ch01_system_integration.dot](../assets/graphviz/ch01_system_integration.dot)

## Interface Port Summary

| Interface | Type | Direction | Data Width | Address Width |
|-----------|------|-----------|------------|---------------|
| Descriptor AXI | AXI4 Master | Read | 256-bit | 64-bit |
| Sink AXI | AXI4 Master | Write | 512-bit | 64-bit |
| Source AXI | AXI4 Master | Read | 512-bit | 64-bit |
| Sink AXIS | AXIS Slave | Input | 512-bit | - |
| Source AXIS | AXIS Master | Output | 512-bit | - |
| Sink CXS (CXS tops only, replaces Sink AXIS) | CXS Receiver | Input | `DATA_WIDTH` (up to 1024-bit) | - |
| Source CXS (CXS tops only, replaces Source AXIS) | CXS Transmitter | Output | `DATA_WIDTH` (up to 1024-bit) | - |
| APB Config | APB-like | Input | 32-bit | 12-bit |
| MonBus | Custom | Output | 64-bit | - |

: External Interface Summary

## Clock and Reset

All interfaces operate in the same clock domain:

| Signal | Type | Description |
|--------|------|-------------|
| `aclk` | input | System clock (100-500 MHz typical) |
| `aresetn` | input | Active-low reset (async assert, sync deassert) |

: Clock and Reset Signals

## Interface Feature Matrix

| Feature | Desc AXI | Sink AXI | Src AXI | Sink AXIS | Src AXIS |
|---------|----------|----------|---------|-----------|----------|
| **Protocol** | AXI4 | AXI4 | AXI4 | AXIS | AXIS |
| **Direction** | Read | Write | Read | Slave | Master |
| **Burst Support** | INCR | INCR | INCR | N/A | N/A |
| **Max Burst** | 1 | 256 | 256 | N/A | N/A |
| **Outstanding** | 8 | 8 | 8 | N/A | N/A |
| **ID Width** | 8-bit | 8-bit | 8-bit | Optional | Optional |

: Interface Feature Matrix

## Signal Count Summary

| Interface | Input Signals | Output Signals | Total |
|-----------|---------------|----------------|-------|
| Descriptor AXI | ~20 | ~30 | ~50 |
| Sink AXI | ~15 | ~40 | ~55 |
| Source AXI | ~25 | ~25 | ~50 |
| Sink AXIS | ~20 | ~5 | ~25 |
| Source AXIS | ~5 | ~20 | ~25 |
| Sink CXS (CXS tops) | ~8 | ~7 | ~15 |
| Source CXS (CXS tops) | ~3 | ~10 | ~13 |
| APB Config | ~15 | ~5 | ~20 |
| MonBus | ~2 | ~5 | ~7 |
| **Total** | **~102** | **~130** | **~232** |

: Signal Count Summary

**Note:** Signal counts are approximate and vary with configuration parameters.
The total counts an AXIS top; a CXS top replaces the two AXIS rows with the
two CXS rows (including the link-status pins).
