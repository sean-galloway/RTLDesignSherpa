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
**Status:** Production Ready

---

## Overview

Both AXIS4 modules have clock-gated (`_cg`) variants that add power management through dynamic clock gating. Same architecture as AXI4/AXIL4 clock gating, optimized for streaming protocols. The deal is simple: when the stream goes quiet, the clock stops; when traffic shows up, the clock restarts and the beat moves.

### Available Clock-Gated Modules

| Module | Base Module | Description |
|--------|-------------|-------------|
| `axis4_master_cg` | [axis4_master](axis4_master.md) | Clock-gated stream master |
| `axis4_slave_cg` | [axis4_slave](axis4_slave.md) | Clock-gated stream slave |

### Key Features

- **Dynamic Clock Gating:** Automatic clock disable during idle
- **Configurable Idle Threshold:** Programmable idle count before gating
- **Functional Equivalence:** Identical data behaviour to the base modules once ungated
- **Status Monitoring:** Real-time `cg_gating` and `cg_idle` indication
- **Low Performance Impact:** A short ungating latency on the first beat after an idle period (see [Clock Gating Behavior](#clock-gating-behavior))

> **No scan-bypass port.** These wrappers have no `cg_test_enable` or equivalent test input.
> For scan/DFT, hold `cfg_cg_enable = 0`, which forces the ICG permanently enabled and makes
> the wrapper functionally identical to the base module.

---

## Parameters

The `_cg` variants add exactly one parameter to the base module's list:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | int | 4 | Width of idle counter (max idle = 2^N-1 cycles) |

**All other parameters identical to base module.**

---

## Ports

### Clock Gating Configuration

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `cfg_cg_enable` | 1 | Input | Enable clock gating (0=disabled, 1=enabled) |
| `cfg_cg_idle_count` | CG_IDLE_COUNT_WIDTH | Input | Idle cycles before gating |

### Clock Gating Status

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `cg_gating` | 1 | Output | Clock currently gated (1=gated, 0=running) |
| `cg_idle` | 1 | Output | No activity was observed in the previous cycle (registered `~wakeup`) |

> **The `_cg` wrappers do not expose `busy`.** The base module's `busy` output is consumed
> internally as one of the wakeup terms and is not brought out. Use `cg_idle` for
> system-level power sequencing instead. Apart from that substitution, and the two
> `cfg_cg_*` inputs above, the port list matches the base module.

> There is **no `cg_clk_count`** port. Cumulative gated-cycle counting is not implemented in
> these wrappers.

---

## Functional Description

### Clock Gating Behavior

Both wrappers build a single `wakeup` term and hand it to `amba_clock_gate_ctrl`. For
`axis4_master_cg` that term is:

```systemverilog
user_valid = fub_axis_tvalid || busy;   // busy is internal; m_axis_tvalid is in axi_valid
axi_valid  = m_axis_tvalid;
wakeup     = user_valid || axi_valid;                    // registered one cycle
```

> **A peer's READY must never appear in the activity term.** A consumer that
> parks its response-ready high while idle is behaving correctly; folding
> that in pins the block permanently awake and defeats gating entirely,
> silently, because function is unaffected. Use the VALID your side drives.
> Ten `_cg` wrappers carried this defect until 2026-09-02.

`axis4_slave_cg` uses the same structure with `s_axis_tvalid`, `fub_axis_tready` and
`fub_axis_tvalid` substituted. Note that the **sink's ready signal is a wakeup term**: a
downstream block holding TREADY high keeps the clock running even with no traffic.

**Gating Conditions (All Must Be True):**
1. No activity on any of the wakeup terms above
2. Idle countdown has expired — gating engages `cfg_cg_idle_count + 1` cycles after the
   internal wakeup deasserts, which is `cfg_cg_idle_count + 2` cycles after the last bus
   activity on AXI4-Stream (one extra for the `r_wakeup` flop)
3. Gating enabled (`cfg_cg_enable = 1`)

**Ungating Conditions (Any Triggers Ungating):**
1. Any wakeup term asserts (TVALID on either side, or a non-empty buffer).
   A peer's TREADY is NOT a wakeup term and must never be one -- see
   `vault/handbook/design/clock-gating-activity-terms.md`.
2. `cfg_cg_enable` deasserted

---

## Timing Characteristics
### Ungating Latency

**Ungating is not instantaneous.** Activity is registered once (AXI4, AXI5, AXI4-Lite,
AXI4-Stream) or twice (APB, APB5, AXI5-Stream) before reaching the ICG enable, which is
combinational. The AXIS4 wrappers drive `user_valid`/`axi_valid` combinationally, so they
sit in the single-stage group:

| Stage | Cost | Source |
|-------|------|--------|
| `wakeup` register in `amba_clock_gate_ctrl` | 1 cycle | `r_wakeup <= user_valid \|\| axi_valid` |
| ICG enable in `clock_gate_ctrl` | 0 cycles (combinational) | `w_gate_enable = cfg_cg_enable && !wakeup && (r_idle_counter == 'h0)` |
| First usable gated-clock rising edge | 1 cycle | The released clock is only usable on the following edge |

**1 register stage; the first usable gated-clock edge arrives 2 `aclk` cycles** after
activity asserts. The `clock_gate_ctrl` header comment "Wakeup: 1 clock from wakeup
assertion to clock restoration" refers to that resulting edge, not to a register stage.

> The AXI5-Stream (`axis5_*_cg`) wrappers register activity locally before handing it to
> `amba_clock_gate_ctrl`, so they are a two-stage design: 3 cycles to the first usable
> edge. See [axis5_master_cg](../axis5/axis5_master_cg.md).

This latency is not free of protocol impact. Both wrappers force the incoming ready signal
low while gated:

```systemverilog
// axis4_master_cg
assign fub_axis_tready = cg_gating ? 1'b0 : int_tready;
// axis4_slave_cg
assign s_axis_tready   = cg_gating ? 1'b0 : int_tready;
```

So the first beat presented after an idle period is **backpressured for the ungating
latency** rather than accepted immediately. Budget this stall when sizing
`cfg_cg_idle_count` for latency-sensitive streams: an aggressive idle count trades
first-beat latency for power.

---

## Usage Examples
```systemverilog
axis4_master_cg #(
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
    .cg_idle(stream_idle)
);
```

---

## Design Notes

### Configuration Guidelines

#### Idle Count Selection for Streaming

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

**Recommended For:**
- Packet-based streaming (idle between packets)
- Video processing (blanking periods between frames/lines)
- Burst data transfers (gaps between bursts)
- Power-constrained streaming applications

**Not Recommended For:**
- Continuous audio/video streams (100% utilization)
- Real-time DSP pipelines (no idle periods)
- Ultra-low-latency paths

The pattern there is honest: gating pays when your stream has gaps. A stream that never idles gives the gate nothing to work with.

### Power Savings Estimates

The figures below are **estimates for planning purposes, not measured power results.** They
have not been correlated against a power analysis run on any target technology.

| Traffic Pattern | Duty Cycle | Idle Count | Estimated Savings |
|-----------------|------------|------------|-------------------|
| Sporadic control stream | 5% | 1 | 60-70% |
| Burst transfers | 30% | 1 | 35-40% |
| Packet network (1500B packets) | 40% | 1 | 30-35% |
| Video (1080p with blanking) | 70% | 5 | 10-15% |
| Continuous stream | 100% | any | 0% (set `cfg_cg_enable = 0`) |

**Notes:**
- Savings apply to the gated clock tree and the sequential elements downstream of it. The
  `amba_clock_gate_ctrl` logic itself, and the wakeup-term combinational cone, remain
  ungated and consume power at all duty cycles.
- Streaming typically has longer continuous active periods than register access, resulting
  in lower power savings than AXI4-Lite.
- At 100% duty cycle, gating never engages, so the wrapper is pure overhead. Instantiate the
  base module instead, or tie `cfg_cg_enable` low.

AXIS-specific notes: the architecture is the same as AXI4/AXIL4 clock gating, power savings
vary based on stream duty cycle, and the best fit is packet-based or frame-based streams.

---

## Related Modules

**For full clock gating details, see:**
- **[AXI4 Clock Gating Guide](../axi4/axi4_clock_gating_guide.md)** - Complete reference
- **[AXIL4 Clock Gating Guide](../axil4/axil4_clock_gating_guide.md)** - Additional examples

### Base Modules
- **[axis4_master](axis4_master.md)** - Base stream master
- **[axis4_slave](axis4_slave.md)** - Base stream slave

### Architecture
- **[AXI4 Clock Gating Guide](../axi4/axi4_clock_gating_guide.md)** - Complete reference
- **[AXIS4 Index](README.md)** - AXIS4 module index

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to AXIS4 Index](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
