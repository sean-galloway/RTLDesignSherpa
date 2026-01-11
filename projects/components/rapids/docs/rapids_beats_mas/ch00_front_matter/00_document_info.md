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

# Document Information

This document describes the RAPIDS "Beats" architecture, a Phase 1 implementation of the Rapid AXI Programmable In-band Descriptor System. The beats architecture provides network-to-memory and memory-to-network data transfer capabilities using descriptor-based DMA with 8-channel support. It emphasizes "beat-level" tracking for precise flow control and latency management.

---

## References

### Related Documents

| Source | Title | Version |
|--------|-------|---------|
| RTL Design Sherpa | RAPIDS Product Requirements Document | 1.0 |
| RTL Design Sherpa | RAPIDS Original Specification | 0.25 |
| RTL Design Sherpa | STREAM MAS (Reference Architecture) | 0.90 |
| ARM | AMBA AXI and ACE Protocol Specification | IHI0022H |
| ARM | AMBA AXI-Stream Protocol Specification | IHI0051A |

: Table 0.1: Related Documents and Specifications

---

## Terminology

**AXIS**

AXI-Stream. ARM's streaming protocol for high-bandwidth, low-latency data transfer without addressing.

**AXI4**

Version 4 of the AXI protocol, supporting burst transfers up to 256 beats.

**Beat**

A single data transfer within an AXI burst. For RAPIDS with 512-bit data width, one beat = 64 bytes.

**Beats Architecture**

The Phase 1 RAPIDS implementation that tracks transfers at beat granularity for precise flow control.

**Burst**

A group of consecutive data transfers (beats) initiated by a single address phase.

**Channel**

One of 8 independent DMA channels in RAPIDS. Each channel has its own descriptor chain and SRAM buffer allocation.

**Descriptor**

A 256-bit data structure containing transfer parameters: address, length, channel ID, and control flags.

**Descriptor Chain**

A linked list of descriptors where each descriptor points to the next, enabling scatter-gather operations.

**DMA**

Direct Memory Access. Hardware-controlled data movement between memory locations without CPU intervention.

**FUB**

Functional Unit Block. A self-contained RTL module with defined interfaces and testbench.

**Latency Bridge**

A module that provides buffering to compensate for pipeline latency between alloc/drain controllers.

**MAC**

Macro. An integration-level block that instantiates and connects multiple FUBs.

**MonBus**

Monitor Bus. A 64-bit internal bus for performance monitoring and debug event reporting.

**RAPIDS**

Rapid AXI Programmable In-band Descriptor System. A DMA accelerator for network-to-memory transfers.

**Sink Path**

The data path from network (AXIS slave) to system memory (AXI write master).

**Source Path**

The data path from system memory (AXI read master) to network (AXIS master).

**SRAM**

Static Random Access Memory. Used for internal data buffering between network and memory interfaces.

**Virtual FIFO**

A tracking mechanism (alloc_ctrl/drain_ctrl) that manages SRAM space without moving actual data.

---

## "Beats" Architecture Concept

The "beats" architecture name reflects the key design decision to track all transfers at **beat granularity** (data-width units) rather than byte or chunk granularity:

1. **Beat-level Allocation:** Space is allocated in beats (e.g., 64-byte units for 512-bit datapath)
2. **Beat-level Drain:** Data availability is tracked in beats
3. **Beat-level Latency:** The latency bridge compensates for pipeline delays in beat counts
4. **Beat-level Completion:** AXI engines report completion in beats

This simplifies the math and aligns naturally with AXI burst semantics where each beat represents one data-width transfer.

---

## Revision History

Revisions follow the convention x.y, where x is the major version and y is the minor version.

| Rev | Date | Author | Notes |
|-----|------|--------|-------|
| 0.25 | 2025-01-10 | seang | Initial RAPIDS Beats MAS structure |

: Table 0.2: RAPIDS Beats MAS Document Revision History

---

**Last Updated:** 2025-01-10
