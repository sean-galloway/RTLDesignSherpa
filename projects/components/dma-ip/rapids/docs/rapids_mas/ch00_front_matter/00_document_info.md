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

This document describes RAPIDS, the byte-granular Rapid AXI Programmable In-band Descriptor System. RAPIDS provides network-to-memory and memory-to-network data transfer using descriptor-based DMA with 8 or 16 channels. A descriptor length is a byte count, source and destination addresses are byte addresses, and the sink write master drives byte enables. The earlier "Beats" architecture, which counted everything in beats, was the stepping stone to this design and is documented separately in the RAPIDS Beats MAS.

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.6 | 2026-10-17 | RTL Design Sherpa | New Section 2.10 Shared Engines (`descriptor_engine_shared`, `ctrlrd_engine_shared`, `ctrlwr_engine_shared`: parameters, ports, per-channel state, operation, measured cost). `SHARED_ENGINES` and `TILE_HDR` added to the core and top parameter tables; 8- and 16-channel top variants; scheduler group marked per-channel-build only; scheduler group array overview corrected (one engine of each kind per array, not per channel) |
| 0.5 | 2026-10-17 | RTL Design Sherpa | New Section 3.14 Tile Packet Header (`TILE_HDR`: header build and decode, cell-issued descriptors, status registers). Scheduler group array: shared descriptor / control-read / control-write engines per half (`SHARED_ENGINES`, default 1), with block diagram |
| 0.4 | 2026-10-16 | RTL Design Sherpa | Shared Sections 3.13 and 4.4 point at the routing and payload-type proposal in the tile's TILE_SPEC Section 11 |
| 0.3 | 2026-10-16 | RTL Design Sherpa | Network planes (rapids TASK-024/025): `rapids_top` / `rapids_cxs_top` generated from `rapids_top_base`; links the shared Network Planes chapter and CXS Interface Specification; block diagrams updated for the planes; the CXS ID mapping is marked provisional. |
| 0.2 | 2026-09-30 | RTL Design Sherpa | Channel reset recovers every error class: `cfg_channel_reset` routed into the AXI read and write engines, both data paths and the SRAM wrappers; scheduler clears sticky flags on the reset. |
| 0.1 | 2026-09-30 | RTL Design Sherpa | First byte-granular MAS. Rewrites the chapters that changed from RAPIDS Beats and links the rest. |
| 0.7 | 2026-10-20 | RTL Design Sherpa | Block diagrams redrawn to the repo element key (v3): class fills, double-bordered registered blocks, green return paths and a generated key under each figure. No technical content changed. |
| 0.8 | 2026-10-20 | RTL Design Sherpa | Section (h2) headings now open a new page, the pipeline default. No technical content changed. |
| 0.81 | 2026-10-21 | RTL Design Sherpa | New Chapter 5, rapids-g: gatling-sequenced schedulers (`scheduler_g`, `rapids_seq_g`, firmware, the generated tree, verification, measured cost). Scheduler: split into the FSM and `scheduler_core`; MonBus events on state entry (rapids BUG-016); run-base generators flushed by the channel reset (rapids BUG-017). |
| 0.82 | 2026-10-22 | RTL Design Sherpa | rapids-g at one hart per channel (NUM_HARTS = NUM_CHANNELS): Section 5.3 describes the one-slot tight loop, with flow charts of the poll loop and `service` (Figures 5.3.1 and 5.3.2), and no longer says the firmware computes beat totals (the hardware does); Section 5.5 gains the Genesys 2 gcompare table for rapids-8ch and rapids-g-8ch (45 points, interleaved sink), sim/board match and the chunk warm-up, the firmware-cost history, and the 8-hart bench and out-of-context results. |
| 0.83 | 2026-10-23 | RTL Design Sherpa | rapids-g firmware as an executive over a policy table (rapids TASK-037): Section 5.3 rewritten (the poll and `step`, `ptab`, the policy table, the never-reached states and `fw_fault`), with new flow charts (Figures 5.3.1 and 5.3.2); the next-address selector and Z-order (TASK-035) in Sections 5.2 and 5.3; 16 channels (TASK-036), with 8 harts x 2 slots the measured default. Section 5.5: the mutation table re-run on the new image, the executive and 16-channel bench tables, out-of-context results at 8 and 16 channels, and the board run of the new image. |
| 0.84 | 2026-10-23 | RTL Design Sherpa | rapids-g firmware loadable live (rapids TASK-038): `FW_WRITABLE`, the `FW_*` registers, the load and its self-test, ROM once final (Section 5.3, Table 5.3.8). The register mailbox section rewritten as the serialized register path: one agent owns the path from command to response, with both arbitration levels and their signals (Tables 5.3.3-5.3.5). The two-slot poll's chain hook and why a chain is serial. Section 5.5: rapids-16ch and rapids-g-16ch on the Genesys 2 (fit, sim == board, MB/s at 16 channels) and the size sweep at 8 and 16 channels (Tables 5.5.8-5.5.10). Table 5.5.6 re-measured on the committed image. Table 5.5.10 extended to 128 KB per descriptor, with the source rows; new Table 5.5.11, the bytes per descriptor at which rapids-g is within 10%, 5% and 1% of rapids. |

: Table 0.1: Revision History

---

## References

### Related Documents

| Source | Title | Version |
|--------|-------|---------|
| RTL Design Sherpa | RAPIDS Beats MAS (shared chapters) | 0.7 |
| RTL Design Sherpa | RAPIDS HAS | 0.93 |
| RTL Design Sherpa | RAPIDS Product Requirements Document | 1.0 |
| ARM | AMBA AXI and ACE Protocol Specification | IHI0022H |
| ARM | AMBA AXI-Stream Protocol Specification | IHI0051A |
| ARM | AMBA CXS Protocol Specification | IHI0079D |

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
