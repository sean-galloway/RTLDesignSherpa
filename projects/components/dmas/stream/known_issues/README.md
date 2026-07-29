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
| [SRAM drain latency-bridge double-count deadlock](resolved/sram_drain_bridge_double_count.md) | `sram_controller_unit.sv` | High | Bridge occupancy added on top of drain-controller occupancy double-counted skid-resident beats, over-draining the drain FIFO. `rd_ptr` overshot `wr_ptr`, permanently corrupting the count and freezing all 8 channels behind the shared in-order W-phase FIFO. Fixed by reporting drain occupancy alone. |

### Active

| Issue | Module | Severity | Summary |
|-------|--------|----------|---------|
| [Extended chained strided (transpose) descriptor corruption](active/extended_chained_transpose.md) | `descriptor_engine.sv` / `scheduler.sv` / `stream_run_addr_gen.sv` | High | With `USE_ROW_COL_MAJOR_ADDRESSING=1`, a strided/per-beat extended (transpose) descriptor reached via `next_ptr` chaining reads the wrong source, writes with holes, and corrupts the preceding descriptor. Directly-kicked transpose and chained ext-contiguous both pass; only chained + strided fails. Silent (no error raised). Repro: `test_stream_top_extended_chained_transpose` (xfail). |
