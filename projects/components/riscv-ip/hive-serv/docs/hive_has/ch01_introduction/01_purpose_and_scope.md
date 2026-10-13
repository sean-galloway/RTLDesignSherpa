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

This Hardware Architecture Specification is the integration contract for the HIVE
subsystem. It specifies:

1. **System architecture** - the hierarchical control plane (one VexRiscv master,
   sixteen SERV monitors) and its position in the RAPIDS/Delta ecosystem
2. **Subsystem architecture** - the four functional blocks (HIVE-C, SERV monitors,
   Control Network, Configuration Manager), their responsibilities, and the
   resource budget on the proof-of-concept FPGA
3. **External interfaces** - top-level interface classes, the AXIS packet type
   encoding, the 256-bit CDA descriptor format, PKT_CONFIG/PKT_STATUS formats,
   and the memory-mapped register spaces
4. **Programming model** - HIVE-C firmware architecture, descriptor scheduling,
   SERV monitor programming, and the network reconfiguration workflow
5. **Performance targets** - latency, throughput, overhead, and monitoring budget
   commitments, plus the tradeoff tables those commitments come from
6. **Integration and verification** - RAPIDS/Delta integration recipes, test
   levels, formal property inventory, and the implementation roadmap

---

## What HIVE Is

HIVE (Hierarchical Intelligent Vector Environment) is a distributed control and
monitoring subsystem for the RAPIDS DMA engine and the Delta Network compute
fabric. One VexRiscv master controller (HIVE-C) coordinates global operations;
sixteen SERV bit-serial cores, one per Delta compute tile, provide distributed
traffic monitoring and inband configuration/status injection. HIVE consumes no
DSP blocks and a minority of FPGA logic, leaving the fabric free for compute.

HIVE lives in `projects/components/riscv-ip/hive-serv/`, beside the RISC-V falcon
suite ladder. It is deliberately **not** a falcon rung: the ladder teaches one
core's microarchitecture per rung, while HIVE *uses* RISC-V cores (VexRiscv and
SERV, both external projects) as building blocks for a control system. The
educational payload here is hierarchical control, distributed monitoring, and
inband control packets — not a new CPU.

### Status: specification phase, no RTL yet

This HAS describes a planned subsystem. No RTL, firmware, or testbenches exist
yet; the companion MAS documents implementation intent to seed that work. Where
a number in this document is a target rather than a measured result, it is said
so. Content migrated here from the earlier v0.3 spec drafts is treated as design
intent and remains subject to change during RTL bring-up.

---

## Scope

### In Scope

- The four HIVE blocks and their responsibilities (HIVE-C, 16× SERV monitors,
  Control Network, Configuration Manager)
- AXIS packet classification (TUSER[1:0]) and routing rules on the Delta Network
- The 256-bit CDA descriptor format and HIVE-C → RAPIDS injection contract
- PKT_CONFIG and PKT_STATUS formats, including the SERV → HIVE-C reporting path
- Network reconfiguration: the 4 virtual contexts and the atomic switch protocol
- HIVE-C firmware architecture, descriptor scheduling policy, and memory map
- Resource budget on the Digilent NexysA7 100T proof-of-concept platform
- Performance targets and the tradeoff tables behind them
- Integration recipes against RAPIDS and Delta, and the verification strategy

### Explicit Non-Goals

The following are **not** provided by HIVE, and integrators must not rely on
them:

| Non-goal | What provides it instead |
|----------|--------------------------|
| Compute elements (DSP MACs, PE arrays) | Delta Network compute tiles; HIVE only monitors and configures them |
| DDR memory controller | RAPIDS' AXI4 memory interface; HIVE never touches DDR directly |
| Data-plane packet switching / routing tables | Delta Network routers; HIVE *writes* their configuration, it does not forward packets |
| General-purpose host OS / driver stack | Bare-metal host commands over UART or AXI4-Lite; no OS driver exists |
| Real-time guarantees (hard deadlines) | Best-effort latency targets; deadline-aware descriptor scheduling is a policy, not a guarantee |
| Cache coherence | None in the PoC; coherent-access flag in the descriptor is reserved for future use |
| RTL, firmware binaries, SimPy models | Planned deliverables; this document is the specification they will be verified against |

: Explicit non-goals of HIVE

---

## Intended Audience

| Audience | Primary use of this document |
|----------|------------------------------|
| System architects | Decide whether HIVE fits the control plane; understand the contracts with RAPIDS and Delta |
| Hardware engineers | Wire `hive_top` into a system; close timing against the interface classes; plan clock domains |
| Firmware engineers | Structure HIVE-C control software; write SERV monitor firmware; link images for both cores |
| Verification engineers | Plan subsystem-level coverage against Chapter 7 and the MAS verification hooks |

: Intended audience

---

## Specification Conventions

- Signal, register, and packet-field names appear in code font exactly as used in
  the RTL plan (`axis_cda_tvalid`, `MODE_SELECT`) so every claim can be grepped
  once RTL lands.
- Hexadecimal values use `0x` or SystemVerilog sizing (`32'hFFFF_FFFE`); packet
  type encodings use sized binary (`2'b01`).
- "Cycle" means one cycle of the relevant clock domain (see MAS clocking chapter
  for the four-domain map); cross-domain latencies are given as approximate
  ranges.
- **Monitor** in this book means an SERV traffic monitor (a HIVE block). The
  repository's verification monitor system (Ocelus) is referred to by name to
  avoid the collision.
- Packet type names follow the Delta convention: `PKT_DATA`, `CDA` (called
  `PKT_DESC` in early drafts), `PKT_CONFIG`, `PKT_STATUS` in TUSER[1:0].

---

**Last Updated:** 2026-10-12
