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

# Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 0.7 | 2026-10-17 | RTL Design Sherpa | Shared engines (`SHARED_ENGINES`, default 1): key features, block diagram components and hierarchy, and the whole-unit diagram; 8- and 16-channel tops; Resource Estimates gains the measured before-and-after builds and Throughput the board comparison of the two |
| 0.6 | 2026-10-17 | RTL Design Sherpa | Tile packet header (`TILE_HDR`): descriptor `ptype` / `op` / destination fields implemented; new 16-Channel Register Map section (`rapids_16ch_top`, `KICK_ENABLE` at 0x080); tile status registers (shared Register Map) |
| 0.5 | 2026-10-16 | RTL Design Sherpa | Routing and payload-type PROPOSAL (not implemented): the tile packet header is defined in the compute-engine tile's TILE_SPEC Section 11; CXS only transports it. Descriptor Format points at the proposed fields |
| 0.4 | 2026-10-16 | RTL Design Sherpa | Network planes and CXS: links the shared CXS Network Interface chapter; block diagram, hierarchy, system context and key features updated for `rapids_top` / `rapids_cxs_top`; all block diagrams updated |
| 0.3 | 2026-10-16 | RTL Design Sherpa | `SRAM_DEPTH` stated as beats per channel, per direction |
| 0.2 | 2026-09-30 | RTL Design Sherpa | Channel reset recovers every error class; the aresetn-only caveats are removed from Error Handling |
| 0.1 | 2026-09-30 | RTL Design Sherpa | Initial release: the byte-granular RAPIDS, split from the RAPIDS Beats HAS |
| 0.8 | 2026-10-20 | RTL Design Sherpa | Block diagrams redrawn to the repo element key (v3): class fills, double-bordered registered blocks, green return paths and a generated key under each figure. No technical content changed. |
| 0.9 | 2026-10-20 | RTL Design Sherpa | Section (h2) headings now open a new page, the pipeline default. No technical content changed. |
| 0.91 | 2026-10-21 | RTL Design Sherpa | New Section 2.3 rapids-g (firmware-sequenced schedulers, register-compatible); 16-channel register differences list `CH_SCRATCH`. |
| 0.92 | 2026-10-22 | RTL Design Sherpa | New Section 6.4 Choosing RAPIDS or rapids-g: a selection guide and the measured Genesys 2 tables for rapids-8ch and rapids-g-8ch (single descriptors, chains, interleaved sink), the schedulers-alone bench and area. Section 2.3: one hardware context per channel; per-descriptor overhead stated. |
| 0.93 | 2026-10-23 | RTL Design Sherpa | Section 5.1: the next-address selector, chunk 0 `[224:217]` (0 = today's addressing; 1 = Z-order on rapids-g; any value a build cannot run is an invalid descriptor, and RAPIDS runs 0 only). Section 2.3 and 6.4: rapids-g-16ch (`rapids_g_16ch_top`, `rapids_g_16ch_cxs_top`), with its schedulers-alone and area numbers beside rapids-16ch; the 8-channel bench and area tables re-measured on the executive firmware. |
| 0.94 | 2026-10-23 | RTL Design Sherpa | Section 2.3: per-descriptor overhead at 16 channels, and loadable firmware (`FW_WRITABLE`, the `FW_*` registers, rapids TASK-038). Section 6.4: rapids-16ch and rapids-g-16ch on the Genesys 2 (Table 6.4.8, the size sweep at 8 and 16 channels; fit and timing) and the 16-channel selection-guide row from those measurements. Table 6.4.6 re-measured on the committed image. Table 6.4.8 extended to 128 KB per descriptor, with the source rows; new Table 6.4.9, the bytes per descriptor at which rapids-g is within 10%, 5% and 1% of rapids. |

: Document Revision History

---

## Change Summary

### Version 0.2 (2026-09-30)

**Channel reset closes the data-path error gap**

- The per-channel reset now reaches the AXI read and write engines and both
  byte data paths. The data read and write response errors and the sink packet
  length error clear on a channel reset, and the channel takes a good
  descriptor afterwards. Error Handling no longer tells software to use
  `aresetn` for these.
- Error Handling gains the list of what a channel reset does to work in
  flight, including the sink tail discard and the unterminated source packet.
- Head-of-line blocking on a shared sink stream is unchanged and stays
  documented.

### Version 0.1 (2026-09-30)

**Initial Release**

- The byte-granular RAPIDS (rapids TASK-019) is the product design. The
  RAPIDS Beats design was its stepping stone and keeps its own book, the
  RAPIDS Beats HAS.
- New chapters where the byte design differs: Product Overview, Key Features,
  System Context, Block Diagram, Data Flow, AXI4 Master Interface, AXIS
  Interface, both use cases, Descriptor Format, Error Handling, Throughput and
  Resource Estimates.
- Chapters unchanged from RAPIDS Beats are linked from the RAPIDS Beats HAS
  rather than copied, so a correction there reaches both books.
- Permanent limitation recorded: TYPE=EXT (row and column striding)
  descriptors stay beat-aligned. Linear descriptors may start at any byte.
