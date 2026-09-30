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

**Document Title:** RAPIDS Hardware Architecture Specification (HAS)
**Document Number:** RAPIDS-HAS-002
**Version:** 0.1
**Date:** 2026-09-30
**Status:** Draft

---

## Purpose

This Hardware Architecture Specification (HAS) defines the external interfaces, system integration requirements, and high-level architecture of RAPIDS, the byte-granular descriptor-driven DMA engine. RAPIDS counts bytes, not beats: a descriptor names a byte length and byte addresses, the write master carries byte enables, and the AXI-Stream ports carry packed bytes with a partial last beat.

RAPIDS Beats, the beat-granular design that came first, remains in the repository and remains supported. Its specification is the RAPIDS Beats HAS. The two designs share most of their external behavior, so this document links the RAPIDS Beats chapters that apply unchanged and rewrites only the chapters where the byte-granular design differs.

## Scope

This document covers:

- External interface specifications (AXI4, AXIS, APB, MonBus) as they apply to the byte-granular design
- System-level block diagrams and data flows, including the byte placement rules
- Programming model and descriptor format (length in bytes)
- Use cases and operational sequences with unaligned transfers
- Performance characteristics and constraints

This document does NOT cover:

- Internal module architecture (see the RAPIDS MAS)
- RTL implementation details (see the RAPIDS MAS)
- The RAPIDS Beats design (see the RAPIDS Beats HAS)
- Verification test plans
- Physical design constraints

## How This Book Relates to RAPIDS Beats

Chapters that are identical for both designs are not copied. The index links them from the RAPIDS Beats HAS, and the table of contents marks each one "(shared with RAPIDS Beats)". When such a chapter names a module, the byte-granular module is the same name without the `_beats` suffix, for example `rapids_top` for `rapids_beats_top`.

Where a shared chapter says a descriptor length is a number of beats, read it as a number of bytes for RAPIDS. Every chapter that carries that distinction is rewritten in this book, so a reader following the RAPIDS chapters in order will not meet the beat unit except in the comparison tables.

## Audience

| Role | Relevance |
|------|-----------|
| System Architect | Primary - system integration |
| Hardware Integration Engineer | Primary - interface connection |
| Software Engineer | Primary - driver development, descriptor construction |
| Verification Engineer | Reference - interface protocols |
| RTL Designer | Reference - external constraints |

: Target Audience

## Document Conventions

### Requirement Levels

| Term | Meaning |
|------|---------|
| **SHALL** | Mandatory requirement |
| **SHOULD** | Recommended but not mandatory |
| **MAY** | Optional feature |

### Signal Directions

- **Input:** Signal driven by external logic into RAPIDS
- **Output:** Signal driven by RAPIDS to external logic

### Byte and Beat Terms

| Term | Meaning |
|------|---------|
| **Beat** | One transfer on a data bus, `DATA_WIDTH/8` bytes wide (`BYTE_LANES`) |
| **Offset** | The low `log2(BYTE_LANES)` bits of a byte address: the lane where a transfer starts |
| **Packet** | The bytes of one descriptor as they appear on an AXI-Stream port, delimited by TLAST |
| **Packet record** | The `{bytes, offset}` pair the scheduler hands each data path for one descriptor |

: Byte and Beat Terms

### Timing Diagrams

Timing diagrams use WaveDrom format with the following conventions:

- `p` = Positive clock edge
- `0/1` = Logic low/high
- `x` = Unknown/don't care
- `=` = Data value (with label)
- `.` = Previous value continues

---

## References

| Document | Description |
|----------|-------------|
| RAPIDS MAS | Micro-architecture Specification for the byte-granular design |
| RAPIDS Beats HAS | Architecture specification for the beat-granular design; source of every shared chapter |
| ARM AMBA AXI4 Specification | AXI4 protocol reference |
| ARM AMBA AXI-Stream Specification | AXIS protocol reference |
| RAPIDS PRD | Product Requirements Document |

: Reference Documents
