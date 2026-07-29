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

# STREAM - Known Issues Tracking

**Last Updated:** 2026-06-29

## Directory Structure

This directory tracks known RTL issues in the STREAM subsystem, organized by
resolution status:

```
known_issues/
├── README.md                          <- This file
├── resolved/                          <- Fixed bugs and completed investigations
│   └── axi_write_engine_wlast_drain.md
└── active/                            <- Unresolved issues and pending enhancements
```

## Index

### Resolved

| Issue | Module | Severity | Summary |
|-------|--------|----------|---------|
| [axi_write_engine WLAST/drain lost-beat deadlock](resolved/axi_write_engine_wlast_drain.md) | `axi_write_engine.sv` | High | Final WLAST beat lost under W-channel backpressure; SRAM drain was decoupled from `m_axi_wvalid`. Fixed by gating drain on the real W handshake. |
| [Extended chained strided (transpose) descriptor corruption](resolved/extended_chained_transpose.md) | `scheduler.sv` | High | `USE_ROW_COL_MAJOR_ADDRESSING=1`: a legacy descriptor ran the run-base generator with stale ext strides, leaving bogus bases in its FIFO that the next chained strided/transpose descriptor consumed (silent data corruption). Fixed by gating the generator start on `w_is_ext`. (TASK-059) |
| [SRAM drain latency-bridge double-count deadlock](resolved/sram_drain_bridge_double_count.md) | `sram_controller_unit.sv` | High | Bridge occupancy added on top of drain-controller occupancy double-counted skid-resident beats, over-draining the drain FIFO. `rd_ptr` overshot `wr_ptr`, permanently corrupting the count and freezing all 8 channels behind the shared in-order W-phase FIFO. Fixed by reporting drain occupancy alone. |

### Active

(none)
