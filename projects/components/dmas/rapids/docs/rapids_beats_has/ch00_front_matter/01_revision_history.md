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

# Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-17 | RTL Design Sherpa | Initial release |
| 0.6 | 2026-07-02 | RTL Design Sherpa | Resynced to RTL top-level integration |
| 0.7 | 2026-07-13 | RTL Design Sherpa | Added the control-descriptor feature (CTRL_READ consumer gate / CTRL_WRITE producer doorbell) |
| 0.8 | 2026-07-13 | RTL Design Sherpa | Added Chapter 6: Performance (throughput targets, latency characteristics, measured resource estimates) |

: Document Revision History

---

## Change Summary

### Version 0.8 (2026-07-13)

**Performance Chapter**

- Added Chapter 6: Performance, mirroring the STREAM HAS performance chapter:
  - Section 6.1 Throughput Targets -- per-interface and aggregate bandwidth
    (512-bit @ 100 MHz = 6.4 GB/s per direction, 12.8 GB/s full-duplex with
    concurrent sink + source), practical single/multi-channel efficiency,
    limiting factors, design targets, and on-silicon golden-CRC validation
    (48/48 configs).
  - Section 6.2 Latency Characteristics -- kick-to-first-beat breakdown,
    control-descriptor latency (`CTRL_READ` retry budget, `CTRL_WRITE`
    doorbell), variability, and worst-case bounds.
  - Section 6.3 Resource Estimates -- measured post-implementation utilization
    from the Nexys A7-100T characterization build (37,555 LUT / 28,683 FF /
    22 BRAM / 0 DSP at NUM_CHANNELS=4, timing met at 100 MHz), per-block
    breakdown, and scaling notes.

### Version 0.7 (2026-07-13)

**Control-Descriptor Feature**

- Documented the control-descriptor opcodes in Descriptor Format (Section 5.1):
  `CTRL_READ` (consumer gate -- poll a memory location until
  `(read & mask) == expected`) and `CTRL_WRITE` (producer doorbell -- single
  32-bit write), for in-memory producer/consumer synchronization without moving
  payload. Added the per-opcode field layouts.
- Added `CTRL_CONFIG` @ 0x240 (`CTRLRD_MAX_TRY[8:0]`, the control-read poll retry
  budget) to the register map (Section 5.2) and a Key Features entry.

### Version 0.6 (2026-07-02)

**RTL Resync**

- Documented the `rapids_beats_top` integration: single APB slave routed to
  descriptor kick-off (0x000-0x03F) and the `rapids_regs` register block (base
  0x100-0x3FF plus monitor regfile @ 0x1000).
- Refreshed the register map with the actual PeakRDL-generated addresses,
  including the monitor regfile at 0x1000 and `SCHED_TIMEOUT_LIMIT` at 0x208.
- Added the MonBus AXI-Lite group (error-drain slave `s_axil_err_*`, capture
  master `m_axil_mon_*`, `mon_irq`) and the USE_AXI_MONITORS-gated rd/wr AXI
  monitors to the block diagram, APB, and MonBus interface chapters.
- Reflected scheduler recoverable write-progress timeout + B-response commit
  gating and functional descriptor prefetch.

### Version 1.0 (2026-01-17)

**Initial Release**

- Complete HAS for RAPIDS Beats Phase 1 architecture
- External interface specifications (AXI4, AXIS, APB, MonBus)
- System block diagrams with Mermaid
- Timing diagrams with WaveDrom
- Programming model and descriptor format
- Use case documentation
