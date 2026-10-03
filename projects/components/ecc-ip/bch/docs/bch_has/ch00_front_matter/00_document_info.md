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

## Binary BCH Codec Hardware Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Binary BCH Codec Hardware Architecture Specification |
| Version | 0.1 (draft) |
| Date | October 3, 2026 |
| Status | Draft -- decisions D1-D6, D8, the D9 bits-per-beat sub-question, and D11 of the PRD are open; this document carries them as parameters |
| Classification | Open Source - MIT License |

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-10-03 | RTL Design Sherpa | First draft, written before any RTL exists. Captures what the PRD has decided (D7: share the reed-solomon GF layer; D9 direction: valid/ready core with optional AXIS and AXI4 adapters; D10 direction: first consumer expected from a future memory-controller project; D12: scrambler out of scope) and carries the undecided items -- field dimension m, correctable bits t, shortening, encoder/decoder mix, erasures, throughput architecture, bits per beat, generator conventions, key-equation solver -- as parameters tied to their PRD decision IDs. Numbers are analytic placeholders; none are measured. |

## Document Purpose

This Hardware Architecture Specification (HAS) is the high-level view of the
Binary BCH codec -- what it is, where it sits, what it presents at its
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

Micro-architecture -- the GF arithmetic, the syndrome and Chien datapaths,
the key-equation solver arrays, FSMs and signal-level timing -- belongs to the
companion Micro-Architecture Specification (MAS), which does not exist yet.
Until it does, this HAS and the PRD are the block-level reference.

## Intended Audience

- System architects deciding where error correction sits in a datapath
- Integrators instantiating the core or one of its adapters
- Verification engineers planning the golden-model comparison
- Anyone judging whether a binary BCH code, and which one, fits a channel

## Related Documents

| Document | Location | Content |
|---|---|---|
| Product Requirements | `../../PRD.md` | the decision table (D1-D12) and the candidate profiles |
| Architecture sketch | `../bch_architecture_sketch.md` | block diagram and reuse map (to be written) |
| References | `../../References/README.md` | the standards and papers, with source and licence |
| CLAUDE.md | `../../CLAUDE.md` | area facts for a session working here |
| Handbook | `vault/handbook/design/` | valid/ready contract, reset and clocking, filelists, generated-RTL discipline |

: Table 0.1: Related documents
