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

## What is Bridge?

**Bridge** is a Python-based multi-protocol crossbar generator that creates parameterized SystemVerilog RTL from human-readable configuration files. It generates AXI4 crossbars with automatic support for:

- **Protocol conversion** - AXI4, AXI4-Lite, and APB slave interfaces
- **Width conversion** - Automatic upsize/downsize for data width mismatches
- **Channel-specific masters** - Write-only, read-only, or full AXI4 masters

## The Problem Bridge Solves

**Manual AXI4 Crossbar Development is Error-Prone:**

Creating an AXI4 crossbar manually requires:
1. Writing 5 separate channel multiplexers (AW, W, B, AR, R)
2. Implementing per-slave arbitration for each channel
3. Managing ID-based response routing for out-of-order support
4. Handling burst locking and interleaving constraints
5. Inserting width converters for data width mismatches
6. Inserting protocol converters for APB/AXI4-Lite mixed systems
7. Wiring hundreds of signals with consistent naming

**Bridge Automates All of This:**
- Define ports and connectivity in configuration files
- Run generator script
- Get production-ready SystemVerilog RTL

## Scope

This specification covers:

- High-level architecture and block organization
- Supported protocols and conversion capabilities
- Interface requirements and signal conventions
- Performance characteristics and resource estimates
- Integration guidelines and verification strategy

## Out of Scope

The following are covered in the companion MAS:

- Detailed FSM state diagrams and transitions
- Signal-level timing diagrams
- Internal pipeline structures
- RTL implementation details
