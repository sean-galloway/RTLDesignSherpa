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

# FPGA Systems Host Layer Specification

**Component:** The shared host-side board and UART layer (`projects/fpga-systems/bin/`)
**Version:** 1.0
**Last Updated:** 2026-09-30
**Status:** Current. The layer is in production use by every board flow in the
repository. One part is explicitly unverified and is flagged where it appears:
the JTAG identity readback's hardware path has never been exercised against a
board, because a board was held throughout its development (tooling TASK-022).

---

## Overview

This is the specification for `projects/fpga-systems/bin/`, the layer every
board flow imports by bare module name. It answers the four questions each flow
used to answer for itself: which port is my board on, how do I read and write
its registers, in what order do my steps run, and which FPGA am I about to
program.

Read this book if you are standing up a new board flow, debugging a flow that
cannot find its board, or trying to understand why the same host program is
expected to run against both a simulation and silicon.

The layer is roughly 1,500 lines of Python across five modules plus two Tcl
scripts and a shell wrapper, with 1,000 lines of hardware-free tests beside it.
It is small. What makes it worth a book is that the rules it enforces are not
obvious from reading it, and every one of them was installed after a specific
failure.

## Document Structure

### Chapter 1: Overview

- [01_overview.md](ch01_overview/01_overview.md) - What this layer is, what the book covers, and the one property it protects
- [02_layering.md](ch01_overview/02_layering.md) - The four layers and the direction rule
- [03_acronyms.md](ch01_overview/03_acronyms.md) - Acronyms, and terms this book uses precisely
- [04_references.md](ch01_overview/04_references.md) - Handbook notes, tracker items, external specifications

### Chapter 2: The UART Flow

- [01_port_discovery.md](ch02_uart_flow/01_port_discovery.md) - Why a port is never hardcoded, USB-serial matching, the Genesys 2 exception
- [02_probes.md](ch02_uart_flow/02_probes.md) - How a board says "yes, I am the one you want", and which probe shape is safe
- [03_link_and_bridge.md](ch02_uart_flow/03_link_and_bridge.md) - UartLink, UARTAxiBridge, and the injection point
- [04_wire_protocol.md](ch02_uart_flow/04_wire_protocol.md) - The ASCII W/R protocol, defaults, and an ambiguous return
- [05_sim_equivalence.md](ch02_uart_flow/05_sim_equivalence.md) - One host program, two transports, and the constraint that follows

### Chapter 3: Sequences

- [01_model.md](ch03_sequences/01_model.md) - The model and the two rules the runner enforces
- [02_context_and_results.md](ch03_sequences/02_context_and_results.md) - What a sequence is given, and what it is deliberately not given
- [03_runner.md](ch03_sequences/03_runner.md) - Registration, resolution before traffic, execution, the report
- [04_writing_one.md](ch03_sequences/04_writing_one.md) - The skeleton, the checklist, and what does not belong

### Chapter 4: Boards

- [01_registry.md](ch04_boards/01_registry.md) - BoardSpec, the two boards in this lab, and their recorded traps
- [02_programming.md](ch04_boards/02_programming.md) - The program path and the order of its checks
- [03_locking_and_identity.md](ch04_boards/03_locking_and_identity.md) - A lock prevents, a readback detects, and why the verdict is persisted

### Chapter 5: Conventions

- [01_naming.md](ch05_conventions/01_naming.md) - Why the filename prefixes are load-bearing, and the measured migration status
- [02_paths.md](ch05_conventions/02_paths.md) - Anchor to a marker, never count directory levels

### Chapter 6: Standing Up a Flow

- [01_new_flow.md](ch06_standing_up/01_new_flow.md) - Ten steps in the order that fails earliest, plus a checklist

---

## Design Notes

### Document Conventions

This book specifies the **layer**. Method lives in `vault/handbook/`, which is
the repository's memory, and where the two meet this book links rather than
restates. A second copy is how documentation rots: the copy nobody edits is the
one the next session reads.

The clearest instance is Chapter 5. The authority for the directory skeleton and
filename conventions is the handbook note `flow-layout`; that chapter records
only what binds those conventions to this layer -- that the prefixes are what
`make` and `SequenceRunner.discover` glob for, so a misnamed file is invisible
rather than merely untidy.

No emojis appear anywhere in this book; they break the LaTeX path that produces
the PDF.

### What this book does not contain

- **Register maps.** Registers are addressed by name through a generated map.
  A register table copied here would be a second source nothing keeps in step.
- **Per-area flows.** What pumice's characterization measures, or what the
  stream monitor campaign proves, belongs to those areas.
- **The FPGA-side RTL.** The bridge that turns the ASCII protocol into AXI4-Lite
  is specified with the RTL.

### Version History

| Version | Date | Change |
| --- | --- | --- |
| 1.0 | 2026-09-30 | First edition. Filed as tooling TASK-024. |

---

## Navigation

### Standing up a new flow

Chapter 6 is the checklist. Read Chapter 2 first if the board is new to the
bench, and Chapter 5 before creating any directories.

### Debugging a flow that cannot find its board

Chapter 2, sections 1 and 2. Start with
`python3 projects/fpga-systems/bin/uart_link.py` and
`fpga_board.py ports --board <name>`; if those print nothing the problem is the
registry or the cabling, not the flow.

### Writing or changing a campaign

Chapter 3. Section 4 is the skeleton and the checklist; section 3 explains why
resolution happens before any traffic reaches the board.

### Trusting a measurement

Chapter 4, section 3. A lock prevents a collision and a readback detects one
that happened anyway; the identity record is what makes "could not look"
distinguishable from "looked and approved" after the fact.
