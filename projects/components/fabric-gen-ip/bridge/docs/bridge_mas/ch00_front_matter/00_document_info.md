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

## Overview

### Bridge Micro-Architecture Specification

| Property | Value |
|---|---|
| Document Title | Bridge Micro-Architecture Specification |
| Version | 1.4 |
| Date | 2026-10-18 |
| Status | Released |
| Classification | Open Source - MIT License |

: Document information

### Document Purpose

This Micro-Architecture Specification (MAS) documents how the Bridge component is built:

- Block-level architecture and internal structure
- FSM state diagrams and transition tables
- ID management (and the CAM architecture that was never built)
- Signal-level interface details
- Width and protocol converter implementation
- Timing diagrams and debug information

Yes, the CAM gets called out in its own bullet — it was documented, never built, and the pages say so rather than letting you go looking for it in the RTL. For high-level architecture, system integration, and performance overview, refer to the companion **Bridge Hardware Architecture Specification (HAS)**.

### Intended Audience

- RTL designers implementing or modifying Bridge
- Verification engineers developing testbenches
- System integrators debugging Bridge behavior
- Technical staff requiring implementation details

## Design Notes

### Revision History

| Version | Date | Author | Description |
|---|---|---|---|
| 1.0 | 2026-01-03 | RTL Design Sherpa | Initial release - restructured from single spec |
| 1.1 | 2026-06-04 | RTL Design Sherpa | Content sync to RTL state at 2026-06-04. Adds (1) monitor-aggregation discussion in the crossbar-core chapter — per-port `axi4_{master,slave}_{rd,wr}_mon` wrappers feed a `monbus_arbiter` tree into a single bridge-top `monbus_axil4_axil4_group`, packet+timestamp carried atomically through a 192-bit skid; references the canonical 128-bit packet spec at `docs/markdown/rtl-amba/includes/ocelus_package_spec.md`; (2) generator-emitted protocol-conversion shims at the slave boundary — `axi4_to_axil4_{rd,wr}` for AXIL slaves, chained with the AXIL→APB shim for APB slaves; (3) AXIL→wider-slave master-side alignment converters in the width-converters chapter (`axil_to_axi4_wide_align_{rd,wr}` — partial-word alignment, not protocol bridging); (4) generated-RTL chapter now lists monitor-variant module emission and per-port `(UNIT_ID, AGENT_ID)` assignment conventions; (5) verification-strategy chapter rewritten for protocol-BFM-only TBs with memory-backed slaves, the new `boundary_probe` test pattern, and the four `test_bridge_*_monitor_*.py` canonical patterns (smoke/capture/error_inject/irq); (6) response-routing chapter notes the independent W-tracker FIFO + split AW/W-ready MUX fix (commit `d24bd617`) that closed an interleaved-master deadlock. |
| 1.2 | 2026-09-08 | RTL Design Sherpa | Correctness and voice pass. Four external qc rounds (65/54/53/57 findings, all triaged against rtl/generated and the generator) removed the planned-but-never-built ID-table/CAM out-of-order scheme, the fixed 64-bit internal path, response arbitration/FIFOs and the AXI4-Lite-as-future-work status from the text; annotated the TOML keys the loader has never known and its three-tier unknown-key behaviour; replaced asserted latency figures with measured ones. Four RTL defects found by the rounds are fixed and mutation-checked (bridge BUG-009 (was BRIDGE-011) response-FIFO overrun, axi4_subtractive_slave simultaneous AW+AR fault loss, axi5_atomic_filter duplicate B and B-before-WLAST). Prose then voice-passed with all correctness annotations preserved. |
| 1.3 | 2026-09-11 | RTL Design Sherpa | bridge TASK-004 (was BRIDGE-014): AXI5-Lite and APB/APB5 as master protocols (front-end converters); bridge TASK-005 (was BRIDGE-016) slave ID widening |
| 1.4 | 2026-09-11 | RTL Design Sherpa | bridge TASK-008 (was BRIDGE-019): Wishbone B4 on both sides of the fabric |
| 1.5 | 2026-09-11 | RTL Design Sherpa | bridge TASK-006 (was BRIDGE-017): measured throughput and latency, registered crossbar, QoS arbitration, CDC slave ports, out-of-context synthesis flow and measured resources, CAM ordering-count fix |
| 1.6 | 2026-09-13 | RTL Design Sherpa | bridge TASK-007 (was BRIDGE-018): native AXI5 fabric -- Memory Tagging and read-data chunking through the structs |
| 1.7 | 2026-09-13 | RTL Design Sherpa | Document sync: one fabric clock plus CDC ports throughout, Wishbone best-effort stance, out-of-order chunk proof |
| 2.0 | 2026-10-12 | RTL Design Sherpa | Protocol-set correction: overview/summary bullets now state the full eight-protocol support (axi3/axi4/axi5/axil/axil5/apb/apb5/wb4 — per-port, slave or master side; ACE coherency NOT supported) verified against `bin/bridge_pkg/config_validator.py`. Version strings aligned across index/front-matter/renders. |
| 1.1 (renumbered) | 2026-10-15 | RTL Design Sherpa | The bridge document set (GAS, HAS, MAS) is renumbered to one common rev, 1.1; rows above keep the numbers they were published under. Content: the one-target-per-master limitation is fixed (GitHub #119 L1) -- per-ID target tracking (`[bridge].id_track_bits`), B/R response arbiters per master width path, the crossed-W hold; the generated TB carries its connectivity map and the generator emits the AXIL narrow-to-wide alignment test (GitHub #119 L8); per-port outstanding limits, `max_outstanding` (power of two 2..64, default 16), size every tracker -- the fixed 16 removed (GitHub #119 L5); per-port `latency` modes (`cut_all` / `cut_ax` / `cut_none`) and honoured TOML skid depths (GitHub #119 L7); read-return-atomic and trace-echo ports no longer limited to one target (GitHub #119 L1b). |
| 1.2 | 2026-10-16 | RTL Design Sherpa | Slave-adapter CAM pipelining (GitHub #119): `bridge_cam` gains `PIPELINE_ALLOC` (registered insert with a pending-entry bypass; the full flag counts the pending entry) and `PIPELINE_FREE` (registered free; lookups see the post-free state), both on in every CAM-tracked slave adapter -- MAS Figure 4.2. HAS 5.1 adds the Genesys 2 fabric-benchmark results against the Xilinx AXI Crossbar and SmartConnect; HAS 5.3 / 6.4 reference synthesis tables re-measured on the current generator. CDC on master ports (GitHub #119 L2): `cdc = true` on an AXI4 master puts `axi4_cdc_{wr,rd}` between the port and its timing wrapper, with `<master>_aclk` / `<master>_aresetn` on the top (HAS 4.5a, MAS 6.1); new fixture `bridge_3x2_rw_mcdc` and `test_bridge_3x2_rw_mcdc_ratio`. Generated TBs build their protocol checkers after reset. Read width converters are built with `R_INTERLEAVE = 0` (no reassembly pool; it had grown every converter fixture past synthesis), so a slave may not interleave R beats across IDs (HAS 4.1, PRD FR-9). |
| 1.3 | 2026-10-16 | RTL Design Sherpa | GitHub #119 L3/L4. Protocol checkers on every port: each bridge gets `<bridge>_checkers.sv`, `axi4_protocol_checker` bound to every AXI4/AXI5 port on its own clock, in simulation and formal only; generated tests use it by default (HAS Verification Strategy, MAS 7.1, GAS 4.1). Slave watchdog: per-slave `timeout_cycles` puts `axi4_slave_watchdog` in front of an AXI4 slave, which answers everything DECERR once the slave is silent that long and raises `<slave>_timeout` (HAS Slave Watchdog, MAS 6.1, GAS 2.2). Measured width-converted path rates and latencies, and accepted throughput and latency against offered load (HAS 5.1). Write-converter B input registered and the master per-ID gate made shallower; HAS 5.3 / 6.4 re-measured. |
| 1.4 | 2026-10-18 | RTL Design Sherpa | Bandwidth limitations addressed. Shared slaves arbitrate at their pins from per-master request slots, so round-robin holds when the slave throttles (a master with two in flight: 0.34 -> 0.50 of the slave; MAS 2.2-2.4, GAS 4.4, HAS 5.1). A narrow master's upsized path into a shared slave gets a rate-matching buffer (`bridge_wr_rate_buf` on writes, a FIFO on reads; `rate_buffer`, default 16 wide beats, 0 off), so the slave runs at its full rate behind it (0.80 -> 0.995 on writes, 0.93 -> 1.000 on reads; MAS 2.6, HAS 2.2, GAS 3.2). Width-converter fixes: the read upsizer's bypass gate and the downsizer's close/reopen of a partial wide beat, both formal-proven. New bandwidth characterization suite `test_bridge_perf_char` in the FUNC regression over nine fixture settings, CDC, AXI3 and AXI5 included, every figure floored (HAS 5.1, MAS 7.1). Open limits (W7-W9 floored at their measured level): W7 (an AXI3 master has one write in flight), W8 (the AXI3 slave converter's issue rate and one-per-ID ordering), W9 (round-robin shares at a CDC slave) and W10 (the AXI3 slave converter uses SystemVerilog queues, which Vivado does not synthesize) (HAS 4.5a, 5.1, 6.5). |

: Revision history

## References

### Related Documents

- **Bridge HAS** - Hardware Architecture Specification (high-level)
- **PRD.md** - Product requirements and overview
- **CLAUDE.md** - AI development guide
