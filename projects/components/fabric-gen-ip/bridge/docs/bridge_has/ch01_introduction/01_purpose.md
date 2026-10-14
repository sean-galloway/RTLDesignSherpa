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

**Bridge** is a Python-based multi-protocol crossbar generator. You describe the interconnect in human-readable configuration files; it hands you back parameterized SystemVerilog RTL. The generated AXI4 crossbars come with automatic support for:

- **Protocol conversion** - AXI3, AXI4, AXI5, AXI4-Lite, AXI5-Lite, APB, APB5, and Wishbone B4 interfaces, on slave or master ports (selected per port in the TOML; ACE coherency is NOT supported)
- **Width conversion** - Automatic upsize/downsize for data width mismatches
- **Channel-specific masters** - Write-only, read-only, or full AXI4 masters

## The Problem Bridge Solves

**A hand-written AXI4 crossbar is error-prone.** Building one means:

1. Writing 5 separate channel multiplexers (AW, W, B, AR, R)
2. Implementing per-slave arbitration for each channel
3. Routing responses back to the issuing master, including slaves that complete different IDs out of order
4. Handling burst locking and interleaving constraints
5. Inserting width converters for data width mismatches
6. Inserting protocol converters for mixed systems — APB/APB5, AXI4-Lite/AXI5-Lite, AXI3, or Wishbone B4 peripherals behind an AXI4 fabric (and vice versa)
7. Wiring hundreds of signals with consistent naming

Every item on that list is a place a bug can sit quietly until integration. I've chased most of them at least once.

**Bridge automates all of it:**

- Define ports and connectivity in configuration files
- Run the generator script
- Get production-ready SystemVerilog RTL

## Scope

This specification covers:

- High-level architecture and block organization
- Supported protocols and conversion capabilities
- Interface requirements and signal conventions
- Performance characteristics and resource estimates
- Integration guidelines and verification strategy

## Out of Scope

These live in the companion MAS:

- Detailed FSM state diagrams and transitions
- Signal-level timing diagrams
- Internal pipeline structures
- RTL implementation details
