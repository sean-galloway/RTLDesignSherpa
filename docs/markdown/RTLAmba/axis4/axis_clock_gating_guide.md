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

# AXIS4 Clock-Gated Variants Guide

**Location:** `rtl/amba/axis4/*_cg.sv`
**Status:** ✅ Production Ready

---

## Overview

Both AXIS4 modules have clock-gated (`_cg`) variants that add power management through dynamic clock gating. Same architecture as AXI4/AXIL4 clock gating, optimized for streaming protocols.

### Available Clock-Gated Modules

| Module | Base Module | Description |
|--------|-------------|-------------|
| `axis_master_cg` | [axis_master](axis_master.md) | Clock-gated stream master |
| `axis_slave_cg` | [axis_slave](axis_slave.md) | Clock-gated stream slave |

### Key Features

- ✅ **Dynamic Clock Gating:** Automatic clock disable during idle
- ✅ **Configurable Idle Threshold:** Programmable idle count before gating
- ✅ **Full Functional Equivalence:** Identical to base modules
- ✅ **Status Monitoring:** Real-time gating status and clock count
- ✅ **Test Mode Support:** Bypass for scan testing
- ✅ **Zero Performance Impact:** Immediate ungating on activity

---

## Additional Parameters (All _cg Modules)

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | int | 4 | Width of idle counter (max idle = 2^N-1 cycles) |

**All other parameters identical to base module.**

---

## Additional Ports (All _cg Modules)

### Clock Gating Configuration

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_cg_enable` | Input | 1 | Enable clock gating (0=disabled, 1=enabled) |
| `cfg_cg_idle_count` | Input | CG_IDLE_COUNT_WIDTH | Idle cycles before gating |

### Clock Gating Status

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cg_gating` | Output | 1 | Clock currently gated (1=gated, 0=running) |
| `cg_clk_count` | Output | 32 | Cumulative gated clock cycles |

**All other ports identical to base module.**

---

## Usage Example

```systemverilog
axis_master_cg #(
    // Base parameters
    .SKID_DEPTH(4),
    .AXIS_DATA_WIDTH(64),
    .AXIS_ID_WIDTH(8),
    .AXIS_DEST_WIDTH(4),
    .AXIS_USER_WIDTH(1),

    // Clock gating
    .CG_IDLE_COUNT_WIDTH(4)  // Up to 15 idle cycles
) u_axis_master_cg (
    .aclk(stream_clk),
    .aresetn(stream_resetn),

    // Clock gating configuration
    .cfg_cg_enable(1'b1),         // Enable gating
    .cfg_cg_idle_count(4'd3),     // Gate after 3 idle cycles

    // AXIS signals (identical to base module)
    .fub_axis_tdata(src_tdata),
    // ... rest of AXIS signals ...

    // Clock gating status
    .cg_gating(stream_clk_gated),
    .cg_clk_count(stream_gated_cycles)
);
```

---

## Clock Gating Behavior

**Gating Conditions (All Must Be True):**
1. Stream idle (no TVALID asserted)
2. Idle for ≥ `cfg_cg_idle_count` consecutive cycles
3. Gating enabled (`cfg_cg_enable = 1`)

**Ungating Conditions (Any Triggers Immediate Ungating):**
1. TVALID asserted (stream activity)
2. Configuration change

**Ungating Latency:** 0 cycles (immediate)

---

## Configuration Guidelines

### Idle Count Selection for Streaming

**Aggressive Gating (Burst Packets):**
```systemverilog
.cfg_cg_idle_count(4'd1)   // Gate after 1 idle cycle
// Use for: Packet networks with gaps between packets
```

**Moderate Gating (Mixed Traffic):**
```systemverilog
.cfg_cg_idle_count(4'd5)   // Gate after 5 idle cycles
// Use for: Video processing with blanking periods
```

**Conservative Gating (Continuous Streams):**
```systemverilog
.cfg_cg_idle_count(4'd10)  // Gate after 10 idle cycles
// Use for: Low-latency continuous data flows
```

**Disable Gating:**
```systemverilog
.cfg_cg_enable(1'b0)
// Use for: 100% utilization continuous streams
```

### When to Use Clock Gating

**✅ Recommended For:**
- Packet-based streaming (idle between packets)
- Video processing (blanking periods between frames/lines)
- Burst data transfers (gaps between bursts)
- Power-constrained streaming applications

**❌ Not Recommended For:**
- Continuous audio/video streams (100% utilization)
- Real-time DSP pipelines (no idle periods)
- Ultra-low-latency paths

---

## Power Savings Estimates

### Typical Savings (Streaming Patterns)

| Traffic Pattern | Duty Cycle | Idle Count | Power Savings |
|-----------------|------------|------------|---------------|
| Packet network (1500B packets) | 40% | 1 | 30-35% |
| Video (1080p with blanking) | 70% | 5 | 10-15% |
| Burst transfers | 30% | 1 | 35-40% |
| Continuous stream | 100% | any | 0% |

**Note:** Streaming typically has longer continuous active periods vs register access, resulting in lower power savings than AXI4-Lite.

---

## Complete Documentation

**For full clock gating details, see:**
- **[AXI4 Clock Gating Guide](../axi4/axi4_clock_gating_guide.md)** - Complete reference
- **[AXIL4 Clock Gating Guide](../axil4/axil4_clock_gating_guide.md)** - Additional examples

**AXIS-specific notes:**
- Same architecture as AXI4/AXIL4 clock gating
- Power savings vary based on stream duty cycle
- Best for packet-based or frame-based streams

---

## Related Documentation

### Base Modules
- **[axis_master](axis_master.md)** - Base stream master
- **[axis_slave](axis_slave.md)** - Base stream slave

### Architecture
- **[AXI4 Clock Gating Guide](../axi4/axi4_clock_gating_guide.md)** - Complete reference
- **[AXIS4 Index](README.md)** - AXIS4 module index

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to AXIS4 Index](README.md)**
- **[← Back to RTLAmba Index](../index.md)**
