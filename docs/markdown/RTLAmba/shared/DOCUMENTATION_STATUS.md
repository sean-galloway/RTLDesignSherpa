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
**Last updated:** 2026-06-11 (monbus_group two-stage burst-sizing fix; new master-write + axi4_axil tests)
**Location:** `/mnt/data/github/RTLDesignSherpa/docs/markdown/RTLAmba/shared/`

---

## Completion Status

### Completed Documentation

1. **axi_monitor_base.md** - COMPLETE
   - Comprehensive module documentation with all sections
   - Usage examples provided
   - Design notes included
   - Cross-references added

11. **axi_monitor_trans_mgr.md** - COMPLETE (rewritten 2026-06-08)
    - Reflects CAM-backed revision (delegates to monitor_trans_cam)
    - Documents synthesis properties carried from the 2026-04-23 WNS fix
    - Equivalence test + TRANS_MGR_VARIANT rollback knob covered

12. **monitor_trans_cam.md** - COMPLETE (new 2026-06-08)
    - Multi-port ID CAM with opaque payload
    - 3 lookup ports + 3-way mutex alloc priority encoder
    - Synthesis notes (keep="true" anchors, per-slot generate-loop storage)

13. **monbus_compressor.md** - COMPLETE (new 2026-06-08)
    - Hardware bulk-trace encoder, ~2.66× compression
    - Full coverage of all 5 compression techniques (template extraction,
      delta-ts, width-tiered Tier-1, differential payload, Tier-0 RAW)
    - Bit layouts, encoder decision tree, pipeline/timing/synthesis notes

14. **monbus_cam.md** - COMPLETE (new 2026-06-08)
    - 32-entry true-LRU caching CAM (position-indexed storage)
    - Backs monbus_compressor's template indexing
    - Caller protocol (NONE/TOUCH/INSTALL), eviction semantics

15. **monbus_group.md** - COMPLETE (rewritten 2026-06-11, was monbus_axil_group.md;
                              refreshed same day for the two-stage burst-sizing fix)
    - Renamed from monbus_axil_group.md to reflect the new family.
    - Covers the full 5-file family: 1 protocol-agnostic core
      (monbus_group_core.sv) + 4 protocol-permutation wrappers
      (axil_axil / axil_axi4 / axi4_axil / axi4_axi4).
    - Documents the beat-granular write FIFO, watermark + timeout
      burst writer (4KB-boundary aware), and AXI4 burst behavior.
    - Migration recipe from the legacy single monbus_axil_group module
      (port-surface changes: cfg_flush_watermark added, FIFO counts
      widened to 16 bits, FIFO_DEPTH_WRITE now in beats, locked 64-bit
      data width).
    - "Master-Write Behavior" section refreshed for the two-stage
      drain plan (drain-cycle plans whole-record beats without a
      MAX_BURST_BEATS cap; per-AW sub-bursts get the cap inside the
      FSM). The "Test" section now lists all five tests in the suite,
      including the new master-write coverage that closed the
      AXIL-master raw-mode deadlock.

16. **sdpram_slave.md** - COMPLETE (new 2026-06-09)
    - Covers the full 5-file family: 1 backend + 4 protocol-specific
      wrappers (axi4_axi4 / axi4_axil / axil_axi4 / axil_axil).
    - Documents why the split exists (SystemVerilog cannot conditionally
      include/exclude ports in a single module declaration).
    - Migration recipe from bare `sdpram_slave` to the matching wrapper.
    - Cross-links from monbus_group.md and monbus_compressor.md
      (the memory-dump ring's canonical backend is `sdpram_slave_axil_axil`).

17. **axi_monitor_reporter.md** - COMPLETE (rewritten 2026-06-11)
    - Reflects the 2026-06-06 sub-block refactor (thin dispatcher +
      6 ENABLE_*_LOGIC-gated detection sub-blocks).
    - Lists the six sub-blocks (error / timeout / compl / threshold /
      perf / debug), their logic shapes, and their gate parameters.
    - Notes the bridge-case savings (ENABLE_ERROR_LOGIC=1, others 0
      drops ~70% LUT/FF).
    - The six sub-block files (axi_monitor_reporter_*.sv) are
      explicitly covered here rather than as individual doc pages,
      since they are private to the reporter family.

### Remaining Documentation (15 modules)

The following modules require documentation following the same pattern as axi_monitor_base.md:

#### Monitor Infrastructure
2. axi_monitor_filtered.md - PENDING
3. axi_monitor_reporter.md - **COMPLETE** (rewritten 2026-06-11, see #17)
   - Now describes the dispatcher + 6 sub-blocks (error / timeout /
     compl / threshold / perf / debug). The six sub-block files
     (axi_monitor_reporter_*.sv) are covered here, not as separate
     doc pages.
4. axi_monitor_timeout.md - PENDING
5. axi_monitor_timer.md - PENDING
6. axi_monitor_trans_mgr.md - **COMPLETE** (rewritten 2026-06-08)
   - See #11 in Completed Documentation above

#### Monitor Bus Delivery + Bulk-Trace Compression (NEW SECTION)
   - monbus_group.md - **COMPLETE** (rewritten 2026-06-11, see #15)
     - Renamed from monbus_axil_group.md; covers the new 5-file
       family (core + 4 wrappers).
   - monbus_compressor.md - **COMPLETE** (new 2026-06-08, see #13)
   - monbus_cam.md - **COMPLETE** (new 2026-06-08, see #14)
   - monitor_trans_cam.md - **COMPLETE** (new 2026-06-08, see #12)

#### Memory / BRAM Slave (NEW SECTION)
   - sdpram_slave.md - **COMPLETE** (new 2026-06-09, see #16)
     - Covers backend (sdpram_slave.sv) + 4 wrappers (axi4_axi4, axi4_axil,
       axil_axi4, axil_axil) in a single doc.

#### Monitor Bus Arbitration (4 modules)
7. arbiter_monbus_common.md - PENDING
8. arbiter_rr_pwm_monbus.md - PENDING
9. arbiter_wrr_pwm_monbus.md - PENDING
10. monbus_arbiter.md - PENDING

#### AXI Utilities (4 modules)
11. axi_gen_addr.md - PENDING
12. axi_master_rd_splitter.md - PENDING
13. axi_master_wr_splitter.md - PENDING
14. axi_split_combi.md - PENDING

#### Infrastructure (2 modules)
15. amba_clock_gate_ctrl.md - PENDING
16. cdc_handshake.md - PENDING

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
- [Back to RTLAmba Index](../index.md)
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
- Formats 64-bit interrupt packets
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

**cdc_handshake.sv**
- Clock domain crossing with handshake protocol
- 3-stage synchronizers for metastability protection
- Separate FSMs for source and destination domains
- Parameterizable data width

---

## Next Steps

1. Create remaining 15 markdown files following the template
2. Create README.md index file for shared infrastructure directory
3. Update parent RTLAmba/README.md to link to shared/ subdirectory
4. Cross-reference all related modules
5. Add usage examples for each module
6. Document integration patterns

---

## Notes

- All RTL source files have been read and analyzed
- Module purposes and key features extracted
- Parameter tables ready for documentation
- Port groupings identified
- Design notes captured
- No emojis used in technical documentation
