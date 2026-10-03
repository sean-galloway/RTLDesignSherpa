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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Document Information

## Binary BCH Codec Micro-Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Binary BCH Codec Micro-Architecture Specification |
| Version | 0.1 (draft) |
| Date | October 3, 2026 |
| Status | Draft — no RTL exists; every structural choice is either carried from the PRD or open and tied to a PRD decision ID |
| Classification | Open Source - MIT License |

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-10-03 | RTL Design Sherpa | First draft, written before any RTL exists. Carries the HAS architecture one level down: per-block signal-level intent, FSM policy, timing, and signal-contract references. Numbers are analytic placeholders derived from parameters; none are measured. |

## Document Purpose

This Micro-Architecture Specification (MAS) is the implementation-level view of
the Binary BCH codec — the HAS (`../bch_has/`) taken one level down. It is the
document an RTL author reads before writing SystemVerilog and a verification
engineer reads before writing assertions.

It covers:

- each functional block's internal structure, signals, and parameters
- the FSM policy for every block: where a state machine is forbidden, where one
  minimal control FSM is permitted, and what replaces FSMs elsewhere
- cycle-level timing and throughput placeholders tied to the open PRD decisions
- the signal-contract posture that will be checked by the generated kmap workbook

## Intended Audience

- RTL implementers writing the encoder, decoder, and GF-datapath blocks
- Verification engineers checking the golden-model equivalence and the formal
  properties in `formal/`
- Architects reviewing whether a candidate D6 throughput or D11 solver choice
  fits a consumer's area/latency target

## Related Documents

| Document | Location | Content |
|---|---|---|
| Product Requirements | `../../PRD.md` | the decision table (D1-D12) and the candidate profiles |
| Hardware Architecture Specification | `../bch_has/bch_has_index.md` | high-level block diagram, data flow, solver options, interfaces, parameters |
| Signal-contract workbook | `../../bch_signal_contracts.xlsx` | generated contract sheets and kmap decision tables |
| Signal-contract generator | `../../gen_bch_signal_contracts_kmaps.py` | Python generator for the workbook |
| References | `../../References/README.md` | the standards and papers, with source and licence |
| CLAUDE.md | `../../CLAUDE.md` | area facts for a session working here |
| Handbook | `vault/handbook/design/` | streaming-no-fsm, minimal-fsm, signal-contracts-and-kmaps, valid-ready contracts |

: Table 0.1: Related documents
