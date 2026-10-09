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

# RAPIDS beats on the Genesys 2 -- The AXIS4 Side

**Version:** 1.0
**Date:** 2026-09-29
**Purpose:** What makes the rapids-beats characterization system a different
build from STREAM's, and not the same harness around a different DUT: the two
AXI4-Stream links, the stream endpoints that drive and check them, the way a
measurement window has to be defined on a stream, and the AXIS observers and
monitor-lites that watch them. The companion book,
`rapids_fpga_system`, covers the board, the harness as a whole, the build
variants and the flow; this one is the stream side in depth.

> The RAPIDS core's own AXIS interface specification is in the MAS
> (`projects/components/dma-ip/rapids/docs/rapids_beats_mas/ch04_interfaces/02_axis_interface_spec.md`);
> the measured numbers are in `reports/perf/README.md`.

---

## Document Organization

### Front Matter
- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Why rapids Is Not STREAM
- [Two Engines, Two Stream Ports, and What That Does to the Harness](ch01_why_different/01_why_different.md)

### Chapter 2: The AXIS4 Interfaces
- [Sink Ingress, Source Egress, tid and tlast, the Monitor-Lites](ch02_axis_interfaces/01_axis_interfaces.md)

### Chapter 3: Stream Stimulus and Checking
- [The Generator, the Checker, the Golden Model and GO](ch03_axis_stimulus/01_axis_stimulus.md)

### Chapter 4: Measuring a Stream
- [The AXIS Meters, the Ingress Window, the AXIS Observers](ch04_axis_measurement/01_axis_measurement.md)

---

## Quick Reference

| Item | Value |
|------|-------|
| AXIS links | `s_axis` into the SINK (DUT is the slave), `m_axis` out of the SOURCE (DUT is the master) |
| Width | 256 bits, `tstrb` 32 bits, since the v2.0 design point (512 before) |
| Sideband | `tid[7:0]` carries the channel, `tdest[3:0]` and `tuser[0]` pass through, `tlast` ends a packet |
| Stimulus | `axis4_master_injector` (harness CSR `GEN_*`), `axis4_slave_pattern_check` (`CHK_*`) |
| Meters | `axis_bus_meter` on each link: cycle buckets plus exact bytes and packets |
| Observers | `axis4_intf_observer`, two ports, per-`tid`, own APB window (`USE_OBSERVERS=1`) |
| In-core | one AXIS monitor-lite per half on MonBus (`USE_AXI_MONITORS=1`, rapids TASK-015) |
| Schedules | sequential (one channel at a time) or interleaved (`GEN_MODE.INTERLEAVE`, `--interleave`) |
