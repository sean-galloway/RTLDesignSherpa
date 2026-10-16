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

# Product Overview

## Introduction

RAPIDS Beats is a high-performance network-to-memory accelerator designed for descriptor-based data movement operations. It bridges network interfaces (AXI-Stream) with system memory (AXI4), enabling efficient DMA transfers without CPU intervention.

The "Beats" architecture represents Phase 1 of the RAPIDS family, optimized for simplicity and throughput in streaming applications.

## System Context

### Figure 1.1.1: RAPIDS Beats in Its System

![RAPIDS Beats in Its System](../assets/graphviz/ch01_product_context.png)

**Source:** [ch01_product_context.dot](../assets/graphviz/ch01_product_context.dot)

## Target Applications

| Application | Description | Key Requirements |
|-------------|-------------|------------------|
| **Network Offload** | Receive packets from network, store to memory | Low latency, high throughput |
| **Scatter-Gather DMA** | Multi-descriptor data movement | Descriptor chaining |
| **Streaming Accelerator** | Front-end for compute engines | Continuous data flow |
| **Protocol Processing** | Header/payload separation | Multi-channel isolation |

: Target Applications

## Architecture Highlights

### Phase 1 "Beats" Simplifications

The Beats architecture prioritizes simplicity over feature completeness:

| Feature | Beats (Phase 1) | Future Phases |
|---------|-----------------|---------------|
| **Transfer Unit** | Full beats only | Chunk-level alignment |
| **Flow Control** | Backpressure-based | Credit management |
| **Address Alignment** | Pre-aligned required | Hardware alignment fixup |
| **Network Interface** | Direct AXIS, or CXS through a swappable network plane | Protocol conversion inside the core |

: Phase 1 Simplifications

### Key Capabilities

1. **8 Independent Channels** - Concurrent transfers with dedicated resources
2. **Descriptor Chaining** - Automatic next-descriptor fetch
3. **Dual Data Paths** - Simultaneous sink (write) and source (read)
4. **Monitor Integration** - Real-time event reporting via MonBus
5. **Swappable Network Plane** - AXI-Stream or CXS (Arm IHI 0079 Issue D) at the top, same core
6. **Error Detection** - Address range checking, AXI error propagation
