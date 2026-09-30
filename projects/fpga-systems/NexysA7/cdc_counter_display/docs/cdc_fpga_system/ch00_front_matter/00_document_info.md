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

| Field | Value |
|-------|-------|
| Title | CDC Counter Display on the Nexys A7 -- The FPGA System |
| Version | 1.0 |
| Date | 2026-09-29 |
| Scope | The CDC demonstration system: the board, the two builds and how far apart they are, the harness around the counters, the five CDC modes, and the watch-it-fail flow |
| Not in scope | The CDC primitives themselves (`rtl/cdc/`, documented per module under `docs/markdown/`); the operator procedure (`docs/cdc_demo_guide/`, `docs/HARNESS.md`) |
| Status | Current |

: Table 0.1: Document information

## Related documents

| Document | Where | What it gives you |
|---|---|---|
| CDC demo operator guide | `docs/cdc_demo_guide/` | the chaptered guide for someone at the board |
| Harness procedure | `docs/HARNESS.md` | CSR map plus the scripted demo procedure |
| CDC failure taxonomy | `docs/CDC_DEMO_TODO.md` | the modes of CDC failure, and "why it sometimes works anyway" |
| Project README | `README.md` | the two-build table and the build/program commands |
| pumice system book | `../../pumice/docs/pumice_fpga_system/` | the same book for the other Nexys A7 project, where the harness is shared rather than per-build |

: Table 0.2: Related documents

## Terminology

**CDC**
Clock domain crossing. Moving a signal from one clock to another where the two
have no fixed phase relationship.

**Harness**
Everything in the bitstream that exists to drive and observe the thing being
demonstrated. `build-demo` has one; `build-phase1` deliberately does not.

**Counter domain**
`cdc_counter_domain.sv` -- one counter on its own clock, with a selectable
value-out crossing. Instantiated four times.

**Mode 0 / NO_CDC**
The value-out path built wrong on purpose: a raw flop per bit, no Gray coding,
no `ASYNC_REG`. The subject of the headline demonstration.

**Control group**
The counters left in a correct mode during an experiment, so that a visible
failure cannot be blamed on the board.

## Revision History

| Version | Date | Change |
|---------|------|--------|
| 1.0 | 2026-09-29 | First edition. |

: Table 0.3: Revision history

## How to read this book

Chapter 1 is the bench, and its one surprise: only one of the two builds needs
the host at all. Chapter 2 is the harness -- the CSR map, the four counter
domains, the clock tree, and the five crossings you can select per counter.
Chapter 3 is the comparison this project exists to support, and it answers the
harness-RTL question in the opposite direction from the pumice system on the
same board. Chapter 4 is the watch-it-fail flow and why each step of it is
shaped the way it is.

Every diagram is a Graphviz source under `assets/graphviz/`, rendered to PNG by
`regenerate_all_graphviz.sh`.
