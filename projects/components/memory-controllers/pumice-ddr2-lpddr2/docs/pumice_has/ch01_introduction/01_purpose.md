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

# Purpose and Scope

## Document Purpose

This Hardware Architecture Specification (HAS) defines the high-level architecture of the DDR2 / LPDDR2 Family Memory Controller. It serves as the primary reference for:

- **System Integration** — understanding the controller's external interfaces and system-level requirements
- **RTL Implementation Planning** — module decomposition, interface contracts, and parameter sweeps
- **Verification Planning** — system-level test scenarios and the characterization sweep matrix
- **Driver Development** — programming model and APB register interface

This document complements the upcoming Micro-Architecture Specification (MAS), which will provide detailed block-level implementation specifics, signal-level pinouts, and timing diagrams.

---

## Scope

This HAS covers a single unified controller that supports both DDR2 and LPDDR2 memory via a build-time `MEMTYPE` parameter. The shared engine includes:

- AXI4 slave frontend
- Address mapper
- Transaction queue with row-hit caching
- FR-FCFS scheduler with parameterizable page policy
- Per-bank state machines with local timing enforcement
- Cross-bank timer pool (tRRD / tFAW / tWTR / tCCD)
- Refresh manager with Elastic deferral and DARP-style per-bank scheduling
- Top-level power-state FSM
- Microprogram-based initialization engine
- Pluggable command encoder (DDR2 ras/cas/we OR LPDDR2 CA bus)
- N-phase output gear stage (`N_PHASES` ∈ {1, 2, 4})
- AXI write / read data paths with CWL / CL alignment
- DFI v2.1 master driver
- APB CSR slave for configuration and observation

The only differences between DDR2 and LPDDR2 build configurations are the command encoder, the init step table, the power-state FSM (specifically Self-Refresh vs Deep Power Down handling), and a small number of mode-register signals. Everything else is shared.

---

## Design Philosophy

This controller is intended as a **characterization-first** design. Algorithmic choices that have meaningful research-backed alternatives — page policy, per-bank refresh policy, refresh deferral depth, transaction queue depth — are exposed as parameters rather than hardcoded. The verification plan includes a benchmark sweep over representative AXI traffic patterns to pick defaults from data, not assumption.

The two specific characterization knobs informed by external research are:

- **`PAGE_POLICY` ∈ {OPEN, CLOSE, HAPPY_HYBRID}** — where HAPPY_HYBRID is the address-bit-based page-closure predictor from Ghasempour et al. (2015).
- **`REFPB_POLICY` ∈ {ROUND_ROBIN, OLDEST_FIRST, DARP}** — where DARP is the dynamic access refresh parallelization scheme from Chang et al. (HPCA 2014).

These are described in detail in Chapter 5.

---

## Audience

This document assumes the reader is familiar with:

- AXI4 protocol semantics (handshakes, burst types, ID-based ordering)
- DFI v2.1 specification (control / write-data / read-data sub-interfaces)
- JEDEC DDR2 (JESD79-2F) and LPDDR2 (JESD209-2F) command tables
- Basic memory-controller concepts (open vs closed page policy, refresh deadlines, bank state machines)

Readers new to these topics should first consult the companion `paging-refresh-notes.md` in the family working area for an entry-point bibliography.
