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

This document is the Micro-Architecture Specification (MAS) for `amber`, a parameterised, blocking, snoopy MESI L1 data cache. It closes the implementation decisions that the [amber Hardware Architecture Specification (HAS)](../../amber_has/amber_has_index.md) deliberately deferred to RTL bring-up: pipeline staging, array banking, the exact control FSM state encoding, replacement-policy implementation details, and the pre-RTL combinational decision-logic contracts captured in the kmap workbook.

---

## References

### Related Documents

| Source | Title | Version |
|--------|-------|---------|
| RTL Design Sherpa | amber Product Requirements Document | 0.5 |
| RTL Design Sherpa | amber Hardware Architecture Specification | 0.5 |
| RTL Design Sherpa | amber Pre-HAS sketch | 1.0 |
| ARM | AMBA AXI and ACE Protocol Specification | IHI0022H |
| gem5 | Ruby `MESI_Two_Level` protocol extract | commit f5c5a6e |

: Related Documents and Specifications

---

## Terminology

**ACE**

AXI Coherency Extensions. The ARM protocol carrying snoop channels (AC/CD/CR) and coherent master transactions.

**AC / CD / CR**

ACE snoop channels: Address Coherent (AC), Coherent Data (CD), Coherent Response (CR).

**CRRESP**

5-bit snoop response carrying DataTransfer, PassDirty, IsShared, WasUnique, and an error bit.

**DT / PD / IS / WU**

CRRESP sub-fields: DataTransfer[0], PassDirty[1], IsShared[2], WasUnique[3].

**FUB**

Functional Unit Block. A self-contained RTL module with a defined interface and testbench.

**GAXI**

House generic-AXI streaming pattern (`wr_valid`/`wr_ready`/`wr_data`, `rd_valid`/`rd_ready`/`rd_data`) used for the CPU-side port.

**LRU / FIFO / RANDOM / tree-PLRU**

Replacement policies supported by `amber_repl`. LRU, FIFO, and RANDOM have cache_sim golden-model parity; tree-PLRU is the timing fallback without a sim golden model today.

**MAC**

Macro. An integration-level block that instantiates and connects multiple FUBs.

**MESI**

Cache coherence states: Modified, Exclusive, Shared, Invalid.

**MonBus**

128-bit packet + 64-bit side-band timestamp monitor bus. `amber_monlite` is a drop-and-count observer that never stalls the observed path.

**Pending-fill bypass register**

Single register held by `amber_control` while a fill is outstanding, allowing snoops to the same line to be answered with the post-fill state before the array is updated.

**RACK / WACK**

ACE read/write acknowledge pulses. In amber's adapters they are auto-pulsed one cycle after the last read beat / B handshake.

**SDPRAM**

Simple dual-port RAM. The house `sdpram_core` primitive is the only allowed tag/data storage.

**Snoop responder**

`amber_snoop_resp`, the ACE-shaped adapter that presents bus-agnostic `{address, type, response, data}` transactions to `amber_core`.

---

## Revision History

| Rev | Date | Author | Notes |
|-----|------|--------|-------|
| 0.5 | 2026-10-06 | seang | Initial amber MAS: index, ch01–ch06, styles, title, and pre-RTL kmap workbook. No RTL yet; all micro-architecture proposals are contracts for the landing implementation. |

: amber MAS Document Revision History

---

**Last Updated:** 2026-10-06
