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

This document describes RAPIDS, the byte-granular Rapid AXI Programmable In-band Descriptor System. RAPIDS provides network-to-memory and memory-to-network data transfer using descriptor-based DMA with 8 channels. A descriptor length is a byte count, source and destination addresses are byte addresses, and the sink write master drives byte enables. The earlier "Beats" architecture, which counted everything in beats, was the stepping stone to this design and is documented separately in the RAPIDS Beats MAS.

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-09-30 | RTL Design Sherpa | First byte-granular MAS. Rewrites the chapters that changed from RAPIDS Beats and links the rest. |

: Table 0.1: Revision History

---

## References

### Related Documents

| Source | Title | Version |
|--------|-------|---------|
| RTL Design Sherpa | RAPIDS Beats MAS (shared chapters) | 0.7 |
| RTL Design Sherpa | RAPIDS HAS | 0.1 |
| RTL Design Sherpa | RAPIDS Product Requirements Document | 1.0 |
| ARM | AMBA AXI and ACE Protocol Specification | IHI0022H |
| ARM | AMBA AXI-Stream Protocol Specification | IHI0051A |

: Table 0.2: Related Documents and Specifications

---

## Terminology

**Beat**

One data transfer of an AXI burst or an AXI-Stream transfer. One beat is `BYTE_LANES` bytes, where `BYTE_LANES = DATA_WIDTH/8`. The board design uses 256 bits, so a beat is 32 bytes.

**Byte offset**

The low `OFF_W` bits of a byte address, where `OFF_W = $clog2(BYTE_LANES)`. It is the lane at which a transfer begins inside its first memory beat.

**Memory beat**

A beat as it appears on the AXI side, aligned to `BYTE_LANES`. A packet that starts at a non-zero offset occupies one more memory beat than a stream of the same length would.

**Stream beat**

A beat as it appears on AXI-Stream, packed from lane 0 with no offset.

**Packet record**

The pair `{bytes, offset}` that the scheduler issues once per DATA descriptor, so the AXIS shifter knows how the memory-side and stream-side layouts relate.

**Spill**

The bytes of a stream beat that did not fit in the current memory beat during ingress shifting. They are held for the next memory beat.

**Channel**

One of 8 independent DMA channels. Each has its own descriptor chain, scheduler and SRAM allocation.

**Descriptor**

A 256-bit structure holding the source address, destination address, length in bytes, next pointer, and control flags.

**TYPE=EXT**

The descriptor type that describes a row/column transfer. It stays beat-aligned by design: addresses are aligned and lengths are multiples of the beat size.

**DMA**

Direct Memory Access. Data movement without processor involvement.

**MonBus**

The 64-bit monitor bus that carries event packets out of the design.

---

## Document Conventions

- Shared chapters are linked from the RAPIDS Beats MAS and marked "(shared with RAPIDS Beats)" in the index. Module names in those chapters carry a `_beats` suffix that this design drops.
- Requirement priorities follow the RAPIDS PRD.
- No emojis appear in this document.
