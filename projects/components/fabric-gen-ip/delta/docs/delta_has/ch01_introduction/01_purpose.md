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

## What is Delta?

**Delta** is a Python-based AXI4-Stream crossbar generator. You provide the number of masters, the number of slaves, the data width, and a few optional sideband knobs; it hands you back parameterized, synthesizable SystemVerilog. The name follows the water theme used elsewhere in RTL Design Sherpa (like RAPIDS): a river delta is where one channel splits into many branches, analogous to crossbar routing.

## The Problem Delta Solves

**A hand-written AXI4-Stream crossbar is error-prone.** Building one means writing per-slave arbitration, packet-atomic grant logic, data multiplexing for TDATA/TVALID/TLAST/TDEST/TID/TUSER, and TREADY backpressure steering — then doing it again every time the master or slave count changes.

**Delta automates all of it:**

- Define the crossbar in a single command line
- Run `bin/delta_generator.py`
- Get production-ready SystemVerilog RTL

## Scope

This specification covers:

- High-level architecture and block organization
- AXI4-Stream protocol support, including the optional base + rich signal sets
- Interface requirements and signal conventions
- Performance characteristics and resource estimates
- Integration guidelines and verification status

## Out of Scope

These live in the companion MAS or are deliberate non-goals:

- Detailed FSM state diagrams and transitions (MAS)
- Signal-level timing diagrams (MAS)
- Internal pipeline structures (MAS)
- AXI4/AXI4-Lite/APB protocol conversion (deliberate non-goal; see Bridge or APB crossbar siblings)
- Dynamic reconfiguration or advanced routing algorithms

## Non-Goal: Memory-Mapped Protocol Conversion

Delta is **AXI4-Stream only**. It does not convert to or from AXI4, AXI4-Lite, or APB. If you need address-mapped fabrics, use the sibling `bridge` or `apbx-xbar` components.
