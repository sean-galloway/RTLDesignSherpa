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

## Reed-Solomon Codec Hardware Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Reed-Solomon Codec Hardware Architecture Specification |
| Version | 0.1 (draft) |
| Date | September 29, 2026 |
| Status | Draft -- decisions D2, D3, D5 and D10 of the PRD are open; this document carries them as parameters |
| Classification | Open Source - MIT License |

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-09-29 | RTL Design Sherpa | First draft, written before any RTL exists. Captures what the PRD has decided (valid/ready core with optional AXIS and AXI4 adapters, symbol width as a parameter with the bus a multiple of it, riBM solver with a Euclidean alternative, scrambler behind an enable, endpoint placement, BCH out of scope) and carries the undecided items -- correctable-symbol count and profile, shortening, erasures, first consumer -- as parameters with candidate values. Numbers are analytic, from the FUB catalog; none are measured. |

## Document Purpose

This Hardware Architecture Specification (HAS) is the high-level view of the
Reed-Solomon codec -- what it is, where it sits, what it presents at its
boundaries, what it costs and how it is configured. It is the document an
integrator reads before instantiating the core in a memory controller, a
compute engine or a link, and the document a verification engineer reads to
know what must be proven.

It covers:

- the encoder and decoder cores and their valid/ready interfaces
- the optional AXI-Stream and AXI4 adapters for standalone use
- the configuration parameters and the candidate code profiles
- throughput, latency and resource estimates and how they scale
- integration requirements, verification strategy and synthesis plan

Micro-architecture -- the GF arithmetic, the riBM and Euclidean arrays, the
Chien and Forney datapaths, FSMs and signal-level timing -- lives in the
companion Micro-Architecture Specification (MAS) at
`../reed_solomon_mas/`, written against the landed RTL. `docs/rs_fub_catalog.md`
remains the bottom-up build plan the MAS checks the tree against.

## Intended Audience

- System architects deciding where error correction sits in a datapath
- Integrators instantiating the core or one of its adapters
- Verification engineers planning the golden-model comparison
- Anyone judging whether an RS code, and which one, fits a channel

## Related Documents

| Document | Location | Content |
|---|---|---|
| Product Requirements | `../../PRD.md` | the decision table (D1-D12) and the candidate profiles |
| FUB catalog | `../rs_fub_catalog.md` | every block bottom-up with what it instantiates |
| Architecture sketch | `../rs_architecture_sketch.md` | block diagram and reuse map |
| References | `../../References/README.md` | the standards and papers, with source and licence |
| Handbook | `vault/handbook/design/` | valid/ready contract, reset and clocking, filelists, generated-RTL discipline |

: Table 0.1: Related documents
