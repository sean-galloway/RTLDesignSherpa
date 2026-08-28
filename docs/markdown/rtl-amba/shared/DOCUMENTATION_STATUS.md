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

# Shared Infrastructure Documentation Status

**Generated:** 2025-10-23
**Last updated:** 2026-06-15 (timing-closure refresh: 3-stage burst-writer pipeline, 2-stage compressor, per-template `delta_ts`, runtime `cfg_compress_en`, math_mod_3_compress helper, new axi4_dma_observer doc)
**Location:** `/mnt/data/github/RTLDesignSherpa/docs/markdown/rtl-amba/shared/`

---

## Completion Status

This is the inventory, not the documentation itself. Every module page stands on its own; this file exists so you can see at a glance what changed, when, and what the RTL notes underneath were extracted from. The entry numbers are the original inventory IDs — they're cross-referenced from elsewhere in this file, so they stay even though the list has gaps.

### Completed Documentation

- **#1 — axi_monitor_base.md** — COMPLETE
  - Comprehensive module documentation with all sections
  - Usage examples provided
  - Design notes included
  - Cross-references added

- **#11 — axi_monitor_trans_mgr.md** — COMPLETE (rewritten 2026-06-08; updated 2026-07 for the cb29e226/95c9490a fixes)
  - Reflects CAM-backed revision (delegates to monitor_trans_cam)
  - Documents synthesis properties carried from the 2026-04-23 WNS fix
  - Same-ID slot separation, oldest-first attribution, command-entry cap, same-cycle AW+W bypass, in-RTL formal properties
  - (The legacy variant, its equivalence test, and the TRANS_MGR_VARIANT rollback knob were deleted in d246a72d)

- **#16 — sdpram_slave.md** — COMPLETE (new 2026-06-09)
  - Covers the full 5-file family: 1 backend + 4 protocol-specific wrappers (axi4_axi4 / axi4_axil / axil_axi4 / axil_axil).
  - Documents why the split exists (SystemVerilog cannot conditionally include/exclude ports in a single module declaration).
  - Migration recipe from bare `sdpram_slave` to the matching wrapper.

- **#17 — axi_monitor_reporter.md** — COMPLETE (rewritten 2026-06-11)
  - Reflects the 2026-06-06 sub-block refactor (thin dispatcher + 6 ENABLE_*_LOGIC-gated detection sub-blocks).
  - Lists the six sub-blocks (error / timeout / compl / threshold / perf / debug), their logic shapes, and their gate parameters.
  - Notes the bridge-case savings (ENABLE_ERROR_LOGIC=1, others 0 drops ~70% LUT/FF).
  - The six sub-block files (axi_monitor_reporter_*.sv) are explicitly covered here rather than as individual doc pages, since they are private to the reporter family.

- **#18 — axi4_dma_observer.md** — RETIRED 2026-08-14 with the module (replaced by axi4_intf_master/slave_observer in projects/components/misc)
  - Standalone, DMA-agnostic observability harness that wraps any AXI4-master DMA from outside the DMA (non-intrusive). Companion to the per-DMA axi_monitor_* family which wraps from inside.
  - Covers the full instantiation pattern: NUM_RD + NUM_WR axi4_master_*_mon taps, monbus_arbiter aggregator, monbus_axil4_axi4_group filter+dump, axi_bus_meter, and axi_perf_latency_hist per port.
  - Documents the runtime rid -> channel map (cfg_rd_rid_per_channel) for read-side per-channel attribution and, for writes, either the built-in AW->W awid order tracker (WR_CH_FROM_AWID=1, no DUT sideband) or the optional dma_wr_active_ch_* sideband.
  - The companion modules axi_bus_meter.sv and axi_perf_latency_hist.sv also have their own standalone pages (axi_bus_meter.md, axi_perf_latency_hist.md) — this doc covers their observer wiring.

### New shared infrastructure (no dedicated page, covered above)

- `rtl/math/math_mod_3_compress.sv` — carry-save-compressor `X mod 3` for 16-bit operands; used by monbus_group_core's whole-record compression
- `rtl/amba/filelists/monbus_group.f` — canonical filelist enumerating the group core's dependency tree (math_adder_carry_save_nbit + math_mod_3_compress + monbus_cam + monbus_compressor + monbus_group_core).

### Remaining Documentation (15 modules)

These modules follow the same pattern as axi_monitor_base.md:

#### Monitor Infrastructure
- **#2** — axi_monitor_filtered.md — DONE
- **#3** — axi_monitor_reporter.md — **COMPLETE** (rewritten 2026-06-11, see #17)
  - Now describes the dispatcher + 6 sub-blocks (error / timeout / compl / threshold / perf / debug). The six sub-block files (axi_monitor_reporter_*.sv) are covered here, not as separate doc pages.
- **#4** — axi_monitor_timeout.md — DONE
- **#5** — axi_monitor_timer.md — DONE
- **#6** — axi_monitor_trans_mgr.md — **COMPLETE** (rewritten 2026-06-08)
  - See #11 in Completed Documentation above

#### Monitor Bus Delivery + Bulk-Trace Compression (NEW SECTION)

Nothing lives here anymore — the monitor-family pages (monbus_group, monbus_compressor, monbus_cam, monitor_trans_cam) moved to `../monitor/` with the monitor RTL. See the note at the bottom of this file.

#### Memory / BRAM Slave (NEW SECTION)
- sdpram_slave.md — **COMPLETE** (new 2026-06-09, see #16)
  - Covers backend (sdpram_core.sv) + 4 wrappers (axi4_axi4, axi4_axil, axil_axi4, axil_axil) in a single doc.

#### Monitor Bus Arbitration (4 modules)
- **#7** — arbiter_monbus_common.md — DONE
- **#8** — arbiter_rr_pwm_monbus.md — DONE
- **#9** — arbiter_wrr_pwm_monbus.md — DONE
- **#10** — monbus_arbiter.md — DONE

#### AXI Utilities (4 modules)
- **#11** — axi_gen_addr.md — DONE
- **#12** — axi_master_rd_splitter.md — DONE
- **#13** — axi_master_wr_splitter.md — DONE
- **#14** — axi_split_combi.md — DONE

#### Infrastructure (2 modules)
- **#15** — amba_clock_gate_ctrl.md — DONE

---

## Documentation Template

Each documentation file should follow this structure (see axi_monitor_base.md as reference):

```markdown
# [Module Name]

**Module:** `[module_name].sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

[Brief description from RTL file header comments]

### Key Features

- Feature 1
- Feature 2
- Feature 3
- Feature 4

---

## Module Purpose

[Detailed purpose - why this module exists, what problem it solves]

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| ... | ... | ... | ... |

---

## Port Groups

### [Group 1 Name]

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| ... | ... | ... | ... |

---

## Functional Description

[How the module works - key behavior, FSM states, protocol details]

---

## Usage Example

```systemverilog
[Realistic instantiation example]
```

---

## Design Notes

### [Important design aspect 1]

[Details]

---

## Related Modules

### Used By
- [List of parent modules]

### Uses
- [List of child modules]

---

## References

### Specifications
- [ARM specs]
- [Internal references]

### Source Code
- RTL: `rtl/amba/shared/[module_name].sv`
- Tests: `val/amba/test_[module_name].py`

---

**Last Updated:** 2025-10-23

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to rtl-amba Index](../index.md)
```

---

## Key Information Extracted from RTL

### Monitor Infrastructure Modules

**axi_monitor_filtered.sv**
- Wraps axi_monitor_base with configurable packet filtering
- 3-level filtering hierarchy: packet type masking, error routing, event code masking
- AXI protocol specific (protocol 3'b000)
- Optional pipeline stage for timing closure

**axi_monitor_reporter.sv**
- Reports events/errors through shared monitor bus
- Detects conditions from transaction table
- Formats 128-bit monitor packets (64-bit side-band timestamp)
- Supports error, completion, timeout, threshold, performance, debug packets
- FIFO buffering with gaxi_fifo_sync
- Event reported feedback to trans_mgr (FIX-001)

**axi_monitor_timeout.sv**
- Monitors transaction table for timeout conditions
- Per-phase timeout detection (address, data, response)
- Uses timer tick from frequency invariant timer
- Configurable timeout thresholds per phase

**axi_monitor_timer.sv**
- Frequency invariant timer for timeout detection
- Uses counter_freq_invariant module
- Generates timing ticks based on frequency selection
- Maintains global timestamp counter

**axi_monitor_trans_mgr.sv**
- Manages transaction tracking table
- Tracks up to MAX_TRANSACTIONS concurrent transactions
- Handles out-of-order completions
- Supports data-before-address scenarios
- Event reported feedback input (FIX-001)

### Monitor Bus Arbitration Modules

**arbiter_monbus_common.sv**
- Comprehensive monitoring for RR and WRR arbiters
- Silicon debug monitor with PROTOCOL_ARB events
- 3-bit protocol field [59:57]
- Event categories: error, timeout, completion, threshold, performance, debug
- Per-client ACK timeout tracking
- Protocol violation detection
- Fairness deviation monitoring
- Grant efficiency tracking

**arbiter_rr_pwm_monbus.sv**
- Round-robin arbiter with PWM control
- Standardized fixed internal configurations
- PWM_WIDTH = 16 bits
- MON_FIFO_DEPTH = 16
- Uses arbiter_monbus_common for monitoring

**arbiter_wrr_pwm_monbus.sv**
- Weighted round-robin arbiter with PWM control
- Per-client weight thresholds
- Standardized fixed internal configurations
- Enhanced debug outputs for silicon debug

**monbus_arbiter.sv**
- Round-robin arbiter for monitor bus interfaces
- Optional input and output skid buffers
- ACK mode operation (grants held until acknowledged)
- 128-bit packet + 64-bit side-band timestamp, carried atomically through a 192-bit skid
- Parameterizable number of clients

### AXI Utilities Modules

**axi_gen_addr.sv**
- Address generation for AXI bursts
- Supports FIXED, INCR, WRAP burst types
- Handles data width conversions
- Calculates next address and aligned address

**axi_master_rd_splitter.sv**
- Splits AXI read transactions across boundary crossings
- Assumptions: aligned addresses, fixed transfer size, incrementing bursts
- No address wraparound handling
- Split information FIFO for tracking
- State machine: IDLE, SPLITTING

**axi_master_wr_splitter.sv**
- Splits AXI write transactions across boundary crossings
- Same assumptions as read splitter
- WLAST generation for split transactions
- Response consolidation (N split responses -> 1 upstream response)
- Error priority: DECERR > SLVERR > EXOKAY > OKAY

**axi_split_combi.sv**
- Pure combinational split decision logic
- Simplified boundary crossing detection
- No wraparound handling
- Comprehensive assertions for validation
- Used by both read and write splitters

### Infrastructure Modules

**amba_clock_gate_ctrl.sv**
- Wrapper for clock_gate_ctrl with AMBA-specific activity monitoring
- Monitors user_valid and axi_valid signals
- Configurable idle countdown
- Generates gated clock output

**Monitor-family pages** (monbus_group, monbus_compressor, monbus_cam, monitor_trans_cam) are NOT tracked here anymore — they live in `../monitor/` with the monitor RTL (`rtl/amba/monitor/`).

## Next Steps

All module pages exist. This file's remaining value is the RTL-extracted module notes above — when a module changes, update its page FIRST and this inventory second (or delete the module's entry here rather than let it rot).

## Notes

- All RTL source files have been read and analyzed
- Module purposes and key features extracted
- Parameter tables ready for documentation
- Port groupings identified
- Design notes captured
- No emojis used in technical documentation
