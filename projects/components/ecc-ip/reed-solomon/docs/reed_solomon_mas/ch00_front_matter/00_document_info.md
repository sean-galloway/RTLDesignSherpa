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

## Reed-Solomon Codec Micro-Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Reed-Solomon Codec Micro-Architecture Specification |
| Version | 0.1 (draft) |
| Date | October 4, 2026 |
| Status | Draft — written retroactively against landed RTL (encoder and decoder cores, both solvers, gate DV green); the `.sv` files cited in this document are the ground truth |
| Classification | Open Source - MIT License |

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-10-04 | RTL Design Sherpa | First draft, written after the RTL landed. Documents the landed micro-architecture block by block: signal-level structure, FSM policy, cycle behavior, and the verification posture. Where the FUB catalog (`docs/rs_fub_catalog.md`, 2026-09-29) and the RTL disagree, the RTL wins and the catalog is noted as the plan this MAS checks. |

## Document Purpose

This Micro-Architecture Specification (MAS) is the implementation-level view
of the Reed-Solomon codec — the HAS (`../reed_solomon_has/`) taken one level
down. It is the document a verification engineer reads before writing
assertions and the document an integrator reads before instantiating a core.

It covers:

- each functional block's internal structure, signals, and parameters, cited to the `.sv` source
- the FSM policy for every block: where a state machine is forbidden, where one
  minimal control FSM is permitted, and what replaces FSMs elsewhere
- cycle-level timing and measured throughput per block
- the verification posture: golden-model equivalence, the dual-solver cross-check, and the contract discipline

## Intended Audience

- Verification engineers extending the cocotb gate suite or writing formal properties
- Integrators wiring the cores or the standalone tops into a consumer
- Architects weighing a KES_ALGO switch, an erasure enable, or an S > 1 throughput profile

## Related Documents

| Document | Location | Content |
|---|---|---|
| Product Requirements | `../../PRD.md` | the decision table (D1-D12) and the candidate profiles |
| Hardware Architecture Specification | `../reed_solomon_has/reed_solomon_has_index.md` | high-level block diagram, data flow, solver options, interfaces, parameters |
| FUB catalog | `../../rs_fub_catalog.md` | the bottom-up build plan this MAS checks the landed tree against |
| Golden model | `../../../dv/tbclasses/rs_model.py` | the Python reference, itself validated against `reedsolo`/`galois` |
| References | `../../References/README.md` | the standards and papers, with source and licence |
| CLAUDE.md | `../../../CLAUDE.md` | area facts for a session working here |
| Handbook | `vault/handbook/design/` | streaming-no-fsm, minimal-fsm, signal-contracts-and-kmaps, valid-ready contracts |

: Table 0.1: Related documents
