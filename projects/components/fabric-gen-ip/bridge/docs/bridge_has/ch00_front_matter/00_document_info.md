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

## Bridge Hardware Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Bridge Hardware Architecture Specification |
| Version | 1.7 |
| Date | 2026-10-18 |
| Status | Released |
| Classification | Open Source - MIT License |

: Document information

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2026-01-03 | RTL Design Sherpa | Initial release - restructured from single spec |
| 1.1 | 2026-06-04 | RTL Design Sherpa | Content sync to RTL state at 2026-06-04. Documents (1) the 64→128-bit monbus packet migration with new 64-bit side-band timestamp wire — referenced via `docs/markdown/rtl-amba/includes/ocelus_package_spec.md`; (2) per-port + global SV-parameter monitor methodology with mandatory `use_monitor` TOML field and `variants = ["no","mon"]` generator selector; (3) generator-emitted AXI4↔AXIL conversion at the slave boundary (was external); (4) new AXIL→wider-slave master-side alignment converters (`axil_to_axi4_wide_align_{rd,wr}`); (5) verification-strategy rewrite to protocol-BFM-only TBs with memory-backed slaves, serial-only execution, per-module cocotb function names, boundary_probe (renamed from address_decode) tests; (6) note of the independent W-tracker FIFO + split AW/W-ready MUX fix (commit `d24bd617`) that closed an interleaved-master deadlock. |
| 1.2 | 2026-09-08 | RTL Design Sherpa | Correctness and voice pass. Four external qc rounds (65/54/53/57 findings, all triaged against rtl/generated and the generator) removed the planned-but-never-built ID-table/CAM out-of-order scheme, the fixed 64-bit internal path, response arbitration/FIFOs and the AXI4-Lite-as-future-work status from the text; annotated the TOML keys the loader has never known and its three-tier unknown-key behaviour; replaced asserted latency figures with measured ones. Four RTL defects found by the rounds are fixed and mutation-checked (bridge BUG-009 (was BRIDGE-011) response-FIFO overrun, axi4_subtractive_slave simultaneous AW+AR fault loss, axi5_atomic_filter duplicate B and B-before-WLAST). Prose then voice-passed with all correctness annotations preserved. |
| 1.3 | 2026-09-11 | RTL Design Sherpa | bridge TASK-004 (was BRIDGE-014): AXI5-Lite and APB/APB5 as master protocols (front-end converters); bridge TASK-005 (was BRIDGE-016) slave ID widening |
| 1.4 | 2026-09-11 | RTL Design Sherpa | bridge TASK-008 (was BRIDGE-019): Wishbone B4 on both sides of the fabric |
| 1.5 | 2026-09-11 | RTL Design Sherpa | bridge TASK-006 (was BRIDGE-017): measured throughput and latency, registered crossbar, QoS arbitration, CDC slave ports, out-of-context synthesis flow and measured resources, CAM ordering-count fix |
| 1.6 | 2026-09-13 | RTL Design Sherpa | bridge TASK-007 (was BRIDGE-018): native AXI5 fabric -- Memory Tagging and read-data chunking through the structs |
| 1.7 | 2026-09-13 | RTL Design Sherpa | Document sync: one fabric clock plus CDC ports throughout, Wishbone best-effort stance, out-of-order chunk proof |
| 2.0 | 2026-10-12 | RTL Design Sherpa | Protocol-set correction: overview/summary bullets now state the full eight-protocol support (axi3/axi4/axi5/axil/axil5/apb/apb5/wb4 — per-port, slave or master side) verified against `bin/bridge_pkg/config_validator.py`; explicit "ACE coherency NOT supported" section added to ch03. Version strings aligned across index/front-matter/renders. |
| 1.1 (renumbered) | 2026-10-15 | RTL Design Sherpa | The bridge document set (GAS, HAS, MAS) is renumbered to one common rev, 1.1; rows above keep the numbers they were published under. Content: the one-target-per-master limitation is fixed (GitHub #119 L1) -- per-ID target tracking (`[bridge].id_track_bits`), B/R response arbiters per master width path, the crossed-W hold; the generated TB carries its connectivity map and the generator emits the AXIL narrow-to-wide alignment test (GitHub #119 L8); per-port outstanding limits, `max_outstanding` (power of two 2..64, default 16), size every tracker -- the fixed 16 removed (GitHub #119 L5); per-port `latency` modes (`cut_all` / `cut_ax` / `cut_none`) and honoured TOML skid depths (GitHub #119 L7); read-return-atomic and trace-echo ports no longer limited to one target (GitHub #119 L1b). |
| 1.2 | 2026-10-16 | RTL Design Sherpa | Slave-adapter CAM pipelining (GitHub #119): `bridge_cam` gains `PIPELINE_ALLOC` (registered insert with a pending-entry bypass; the full flag counts the pending entry) and `PIPELINE_FREE` (registered free; lookups see the post-free state), both on in every CAM-tracked slave adapter -- MAS Figure 4.2. HAS 5.1 adds the Genesys 2 fabric-benchmark results against the Xilinx AXI Crossbar and SmartConnect; HAS 5.3 / 6.4 reference synthesis tables re-measured on the current generator. CDC on master ports (GitHub #119 L2): `cdc = true` on an AXI4 master puts `axi4_cdc_{wr,rd}` between the port and its timing wrapper, with `<master>_aclk` / `<master>_aresetn` on the top (HAS 4.5a, MAS 6.1); new fixture `bridge_3x2_rw_mcdc` and `test_bridge_3x2_rw_mcdc_ratio`. Generated TBs build their protocol checkers after reset. Read width converters are built with `R_INTERLEAVE = 0` (no reassembly pool; it had grown every converter fixture past synthesis), so a slave may not interleave R beats across IDs (HAS 4.1, PRD FR-9). |
| 1.3 | 2026-10-16 | RTL Design Sherpa | GitHub #119 L3/L4. Protocol checkers on every port: each bridge gets `<bridge>_checkers.sv`, `axi4_protocol_checker` bound to every AXI4/AXI5 port on its own clock, in simulation and formal only; generated tests use it by default (HAS Verification Strategy, MAS 7.1, GAS 4.1). Slave watchdog: per-slave `timeout_cycles` puts `axi4_slave_watchdog` in front of an AXI4 slave, which answers everything DECERR once the slave is silent that long and raises `<slave>_timeout` (HAS Slave Watchdog, MAS 6.1, GAS 2.2). Measured width-converted path rates and latencies, and accepted throughput and latency against offered load (HAS 5.1). Write-converter B input registered and the master per-ID gate made shallower; HAS 5.3 / 6.4 re-measured. |
| 1.4 | 2026-10-18 | RTL Design Sherpa | Bandwidth limitations addressed. Shared slaves arbitrate at their pins from per-master request slots, so round-robin holds when the slave throttles (a master with two in flight: 0.34 -> 0.50 of the slave; MAS 2.2-2.4, GAS 4.4, HAS 5.1). A narrow master's upsized path into a shared slave gets a rate-matching buffer (`bridge_wr_rate_buf` on writes, a FIFO on reads; `rate_buffer`, default 16 wide beats, 0 off), so the slave runs at its full rate behind it (0.80 -> 0.995 on writes, 0.93 -> 1.000 on reads; MAS 2.6, HAS 2.2, GAS 3.2). Width-converter fixes: the read upsizer's bypass gate and the downsizer's close/reopen of a partial wide beat, both formal-proven. New bandwidth characterization suite `test_bridge_perf_char` in the FUNC regression over nine fixture settings, CDC, AXI3 and AXI5 included, every figure floored (HAS 5.1, MAS 7.1). Open limits (W7-W9 floored at their measured level): W7 (an AXI3 master has one write in flight), W8 (the AXI3 slave converter's issue rate and one-per-ID ordering), W9 (round-robin shares at a CDC slave) and W10 (the AXI3 slave converter uses SystemVerilog queues, which Vivado does not synthesize) (HAS 4.5a, 5.1, 6.5). |
| 1.5 | 2026-10-18 | RTL Design Sherpa | AXI3 limitations addressed. An AXI3 master's writes overlap: `axi3_to_axi4_wr` passes every channel through (W7; was one write in flight, 0.111 beat/cycle single-beat). The AXI3 slave converter takes one request per cycle and passes unchopped requests straight to the pins, with up to 32 in flight across IDs (W8; was every other cycle, one per ID, four requests queued behind the arbiter). Its storage is `gaxi_fifo_sync`, so AXI3 slaves synthesize (W10). An AXI3 slave adapter is built like an AXI4 one: timing wrapper, per-ID tracking and request slots, with the converter last before the pins (W11). Every AXI3 path runs at 1.000 on 2+ beat bursts; round-robin at a shared AXI3 slave holds (HAS 5.1, 6.5; MAS 2.7; GAS 3.4). `max_outstanding` sizing rule with a measured in-flight sweep (HAS 5.1). W9 (CDC-slave round-robin) remains open, with the depth measurement that shows it needs slave-domain arbitration. |
| 1.6 | 2026-10-18 | RTL Design Sherpa | Shared-slave response routing reads the master off the ID (W12). Every fabric ID is `{master index, master id}`, so a multi-master AXI3/AXI4/AXI5 slave adapter (or an `enable_ooo` one) takes the master index from the returned BID / RID's prefix bits and bounds its outstanding count with one counter per direction. The per-ID CAM (`bridge_cam`) it replaces had been the fabric's critical path; on the Artix-7 at 10 ns `bridge_2x2_axi3_slaves` goes from -1.006 to +0.001 ns and `bridge_mix_e` from -2.686 to -0.669 ns, each 1,800-2,100 LUTs smaller (HAS 5.1, 6.4; MAS 2.5, 2.8, 4.1, 4.2; GAS 3.4, 4.4). W13 (`bridge_mix_e`'s remaining paths, in the AXI3 slave converter) is open. `bridge_cam.sv` stays in `rtl/` with its unit test; no generated bridge instantiates it. |
| 1.7 | 2026-10-18 | RTL Design Sherpa | Every open bridge limit closed. W9: a CDC slave that several masters share is crossed per master and arbitrated on its own clock (`bridge_cdc_slave_arb`, `arbiter_matrix`), so round-robin holds there (0.496-0.500 at 32-cycle slave latency, was 0.18-0.20; HAS 4.5a, MAS 2.3, 6.1). W13: the AXI3 slave converter stages chopped requests and merges B and R per entry from registers. W14: APB / AXI4-Lite / WB4 slaves are picked from request slots too, with no early-W bypass. `bridge_2x2_axi3_slaves`, `bridge_mix_e`, `bridge_2x2_rw_cdc` and `bridge_2x2_axi3_masters` all meet 10 ns on the Artix-7 (HAS 5.1). Unused code moved to `deprecated/` (bridge_cam with its test and proof, the analytical model). |

: Revision history

## Document Purpose

This Hardware Architecture Specification (HAS) is the high-level view of the Bridge component — the map you read before you integrate, not the schematic. It covers:

- System-level architecture and data flow
- Protocol support (AXI3, AXI4, AXI5, AXI4-Lite, AXI5-Lite, APB, APB5, Wishbone B4 — per-port, slave or master side; ACE coherency NOT supported)
- Interface definitions and requirements
- Performance characteristics
- Integration guidelines

For micro-architecture, FSM designs, and signal-level detail, see the companion **Bridge Micro-Architecture Specification (MAS)**.

## Intended Audience

- System architects defining interconnect topology
- Hardware engineers integrating Bridge into SoC designs
- Verification engineers planning test strategies
- Technical managers evaluating Bridge capabilities

## Related Documents

- **Bridge MAS** - Micro-Architecture Specification (detailed block-level)
- **PRD.md** - Product requirements and overview
- **CLAUDE.md** - AI development guide
