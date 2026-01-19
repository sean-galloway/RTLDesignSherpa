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

This document describes the STREAM subsystem, a Scatter-gather Transfer Rapid Engine for AXI Memory. STREAM provides descriptor-based DMA functionality with multi-channel support, enabling efficient memory-to-memory data transfers via AXI4 interfaces. The subsystem is designed as a tutorial-focused implementation with intentional simplifications for educational purposes.

---

## References

### Related Documents

| Source | Title | Version |
|--------|-------|---------|
| RTL Design Sherpa | STREAM Product Requirements Document | 1.0 |
| RTL Design Sherpa | RAPIDS MAS (Parent Architecture) | 0.90 |
| ARM | AMBA AXI and ACE Protocol Specification | IHI0022H |
| ARM | AMBA APB Protocol Specification | IHI0024C |

: Related Documents and Specifications

---

## Terminology

**AXI**

Advanced eXtensible Interface. ARM's high-performance, high-frequency protocol for interconnect.

**AXI4**

Version 4 of the AXI protocol, supporting burst transfers up to 256 beats.

**AXIL**

AXI4-Lite. A simplified subset of AXI4 for low-throughput register access.

**APB**

Advanced Peripheral Bus. ARM's simple, low-power bus protocol for peripheral register access.

**Beat**

A single data transfer within an AXI burst. For STREAM with 512-bit data width, one beat = 64 bytes.

**Burst**

A group of consecutive data transfers (beats) initiated by a single address phase.

**Channel**

One of 8 independent DMA channels in STREAM. Each channel has its own descriptor chain and SRAM buffer allocation.

**Descriptor**

A 256-bit data structure containing transfer parameters: source address, destination address, length, and chain pointer.

**Descriptor Chain**

A linked list of descriptors where each descriptor points to the next, enabling scatter-gather operations.

**DMA**

Direct Memory Access. Hardware-controlled data movement between memory locations without CPU intervention.

**FUB**

Functional Unit Block. A self-contained RTL module with defined interfaces and testbench.

**MAC**

Macro. An integration-level block that instantiates and connects multiple FUBs.

**MonBus**

Monitor Bus. A 64-bit internal bus for performance monitoring and debug event reporting.

**Outstanding Transaction**

A transaction that has been issued but not yet completed. V2/V3 performance modes support multiple outstanding transactions.

**Scatter-Gather**

A DMA technique where non-contiguous memory regions are transferred using a descriptor chain.

**SRAM**

Static Random Access Memory. Used for internal data buffering between read and write datapaths.

**V1/V2/V3**

STREAM performance modes:
- V1 (Low): Single outstanding transaction, tutorial-focused
- V2 (Medium): Command pipelined, best area efficiency
- V3 (High): Out-of-order completion, maximum throughput

---

## Revision History

Revisions follow the convention x.y, where x is the major version and y is the minor version. Minor versions indicate incremental updates; major versions indicate significant architectural changes.

| Rev | Date | Author | Notes |
|-----|------|--------|-------|
| 0.90 | 2025-11-22 | seang | Initial STREAM MAS structure and block documentation |
| 0.91 | 2026-01-02 | seang | Added front matter, figure/table captions, document styling |

: STREAM MAS Document Revision History

---

**Last Updated:** 2026-01-02
