# Shared Infrastructure Documentation Status

**Generated:** 2025-10-23
**Location:** `/mnt/data/github/rtldesignsherpa/docs/markdown/RTLAmba/shared/`

---

## Completion Status

### Completed Documentation

1. **axi_monitor_base.md** - COMPLETE
   - Comprehensive module documentation with all sections
   - Usage examples provided
   - Design notes included
   - Cross-references added

### Remaining Documentation (15 modules)

The following modules require documentation following the same pattern as axi_monitor_base.md:

#### Monitor Infrastructure (5 modules remaining)
2. axi_monitor_filtered.md - PENDING
3. axi_monitor_reporter.md - PENDING
4. axi_monitor_timeout.md - PENDING
5. axi_monitor_timer.md - PENDING
6. axi_monitor_trans_mgr.md - PENDING

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
- [Back to RTLAmba Index](../README.md)
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
- 64-bit monitor bus packet interface
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
