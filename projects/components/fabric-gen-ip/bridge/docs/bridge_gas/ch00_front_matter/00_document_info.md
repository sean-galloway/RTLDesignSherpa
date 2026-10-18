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

## Bridge Generator Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Bridge Generator Architecture Specification |
| Version | 1.6 |
| Date | 2026-10-18 |
| Status | Released |
| Classification | Open Source - MIT License |

: Document information

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2026-10-12 | RTL Design Sherpa | Initial GAS release — generator code paths verified against `bridge_generator.py`, `bridge_pkg/config.py`, `bridge_pkg/config_validator.py`, `bridge_pkg/config_loader.py`, and emitted artifacts in `rtl/generated/bridge_mix_e/`. |
| 1.1 (renumbered) | 2026-10-15 | RTL Design Sherpa | The bridge document set (GAS, HAS, MAS) is renumbered to one common rev, 1.1; rows above keep the numbers they were published under. Content: the one-target-per-master limitation is fixed (GitHub #119 L1) -- per-ID target tracking (`[bridge].id_track_bits`), B/R response arbiters per master width path, the crossed-W hold; the generated TB carries its connectivity map and the generator emits the AXIL narrow-to-wide alignment test (GitHub #119 L8); per-port outstanding limits, `max_outstanding` (power of two 2..64, default 16), size every tracker -- the fixed 16 removed (GitHub #119 L5); per-port `latency` modes (`cut_all` / `cut_ax` / `cut_none`) and honoured TOML skid depths (GitHub #119 L7); read-return-atomic and trace-echo ports no longer limited to one target (GitHub #119 L1b). |
| 1.2 | 2026-10-16 | RTL Design Sherpa | Slave-adapter CAM pipelining (GitHub #119): `bridge_cam` gains `PIPELINE_ALLOC` (registered insert with a pending-entry bypass; the full flag counts the pending entry) and `PIPELINE_FREE` (registered free; lookups see the post-free state), both on in every CAM-tracked slave adapter -- MAS Figure 4.2. HAS 5.1 adds the Genesys 2 fabric-benchmark results against the Xilinx AXI Crossbar and SmartConnect; HAS 5.3 / 6.4 reference synthesis tables re-measured on the current generator. CDC on master ports (GitHub #119 L2): `cdc = true` on an AXI4 master puts `axi4_cdc_{wr,rd}` between the port and its timing wrapper, with `<master>_aclk` / `<master>_aresetn` on the top (HAS 4.5a, MAS 6.1); new fixture `bridge_3x2_rw_mcdc` and `test_bridge_3x2_rw_mcdc_ratio`. Generated TBs build their protocol checkers after reset. Read width converters are built with `R_INTERLEAVE = 0` (no reassembly pool; it had grown every converter fixture past synthesis), so a slave may not interleave R beats across IDs (HAS 4.1, PRD FR-9). |
| 1.3 | 2026-10-16 | RTL Design Sherpa | GitHub #119 L3/L4. Protocol checkers on every port: each bridge gets `<bridge>_checkers.sv`, `axi4_protocol_checker` bound to every AXI4/AXI5 port on its own clock, in simulation and formal only; generated tests use it by default (HAS Verification Strategy, MAS 7.1, GAS 4.1). Slave watchdog: per-slave `timeout_cycles` puts `axi4_slave_watchdog` in front of an AXI4 slave, which answers everything DECERR once the slave is silent that long and raises `<slave>_timeout` (HAS Slave Watchdog, MAS 6.1, GAS 2.2). Measured width-converted path rates and latencies, and accepted throughput and latency against offered load (HAS 5.1). Write-converter B input registered and the master per-ID gate made shallower; HAS 5.3 / 6.4 re-measured. |
| 1.4 | 2026-10-18 | RTL Design Sherpa | Bandwidth limitations addressed. Shared slaves arbitrate at their pins from per-master request slots, so round-robin holds when the slave throttles (a master with two in flight: 0.34 -> 0.50 of the slave; MAS 2.2-2.4, GAS 4.4, HAS 5.1). A narrow master's upsized path into a shared slave gets a rate-matching buffer (`bridge_wr_rate_buf` on writes, a FIFO on reads; `rate_buffer`, default 16 wide beats, 0 off), so the slave runs at its full rate behind it (0.80 -> 0.995 on writes, 0.93 -> 1.000 on reads; MAS 2.6, HAS 2.2, GAS 3.2). Width-converter fixes: the read upsizer's bypass gate and the downsizer's close/reopen of a partial wide beat, both formal-proven. New bandwidth characterization suite `test_bridge_perf_char` in the FUNC regression over nine fixture settings, CDC, AXI3 and AXI5 included, every figure floored (HAS 5.1, MAS 7.1). Open limits (W7-W9 floored at their measured level): W7 (an AXI3 master has one write in flight), W8 (the AXI3 slave converter's issue rate and one-per-ID ordering), W9 (round-robin shares at a CDC slave) and W10 (the AXI3 slave converter uses SystemVerilog queues, which Vivado does not synthesize) (HAS 4.5a, 5.1, 6.5). |
| 1.5 | 2026-10-18 | RTL Design Sherpa | AXI3 limitations addressed. An AXI3 master's writes overlap: `axi3_to_axi4_wr` passes every channel through (W7; was one write in flight, 0.111 beat/cycle single-beat). The AXI3 slave converter takes one request per cycle and passes unchopped requests straight to the pins, with up to 32 in flight across IDs (W8; was every other cycle, one per ID, four requests queued behind the arbiter). Its storage is `gaxi_fifo_sync`, so AXI3 slaves synthesize (W10). An AXI3 slave adapter is built like an AXI4 one: timing wrapper, per-ID tracking and request slots, with the converter last before the pins (W11). Every AXI3 path runs at 1.000 on 2+ beat bursts; round-robin at a shared AXI3 slave holds (HAS 5.1, 6.5; MAS 2.7; GAS 3.4). `max_outstanding` sizing rule with a measured in-flight sweep (HAS 5.1). W9 (CDC-slave round-robin) remains open, with the depth measurement that shows it needs slave-domain arbitration. |
| 1.6 | 2026-10-18 | RTL Design Sherpa | Shared-slave response routing reads the master off the ID (W12). Every fabric ID is `{master index, master id}`, so a multi-master AXI3/AXI4/AXI5 slave adapter (or an `enable_ooo` one) takes the master index from the returned BID / RID's prefix bits and bounds its outstanding count with one counter per direction. The per-ID CAM (`bridge_cam`) it replaces had been the fabric's critical path; on the Artix-7 at 10 ns `bridge_2x2_axi3_slaves` goes from -1.006 to +0.001 ns and `bridge_mix_e` from -2.686 to -0.669 ns, each 1,800-2,100 LUTs smaller (HAS 5.1, 6.4; MAS 2.5, 2.8, 4.1, 4.2; GAS 3.4, 4.4). W13 (`bridge_mix_e`'s remaining paths, in the AXI3 slave converter) is open. `bridge_cam.sv` stays in `rtl/` with its unit test; no generated bridge instantiates it. |

: Revision history

## Document Purpose

This Generator Architecture Specification (GAS) is the manual for the Bridge **code generator**. It is written for the engineer who must:

- re-run the generator after a bugfix,
- add a new protocol or port option,
- debug a generated module,
- or audit why a particular file was emitted.

It covers the full generator surface: CLI flags, TOML keys, Python data classes, validation rules, emission stages, output files, and the extension points that are safe to touch.

For the hardware that the generator produces, see the **Bridge HAS** and **Bridge MAS**. For product requirements, see **PRD.md**.

## Intended Audience

- RTL engineers modifying or extending the generator
- Verification engineers regenerating fixtures after a generator change
- System architects adding new bridge configurations to the batch
- Integrators debugging a generated bridge top

## Related Documents

- **Bridge HAS** - Hardware Architecture Specification
- **Bridge MAS** - Micro-Architecture Specification
- **PRD.md** - Product requirements and overview
- **CLAUDE.md** - AI development guide and subsystem rules
