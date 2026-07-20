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

# AXIL4 Clock-Gated Variants Guide

**Location:** `rtl/amba/axil4/*_cg.sv`
**Status:** ✅ Production Ready

---

## Overview

All AXIL4 modules have clock-gated (`_cg`) variants that add power management through dynamic clock gating. Identical architecture to **[AXI4 Clock Gating](../axi4/axi4_clock_gating_guide.md)** but optimized for AXI4-Lite's simpler protocol.

### Available Clock-Gated Modules

| Module | Base Module | Description |
|--------|-------------|-------------|
| `axil4_master_rd_cg` | [axil4_master_rd](axil4_master_rd.md) | Clock-gated read master |
| `axil4_master_wr_cg` | [axil4_master_wr](axil4_master_wr.md) | Clock-gated write master |
| `axil4_slave_rd_cg` | [axil4_slave_rd](axil4_slave_rd.md) | Clock-gated read slave |
| `axil4_slave_wr_cg` | [axil4_slave_wr](axil4_slave_wr.md) | Clock-gated write slave |
| `axil4_master_rd_mon_cg` | [axil4_master_rd_mon](../monitor/axil4_master_rd_mon.md) | Clock-gated read master + monitor |
| `axil4_master_wr_mon_cg` | [axil4_master_wr_mon](../monitor/axil4_master_wr_mon.md) | Clock-gated write master + monitor |
| `axil4_slave_rd_mon_cg` | [axil4_slave_rd_mon](../monitor/axil4_slave_rd_mon.md) | Clock-gated read slave + monitor |
| `axil4_slave_wr_mon_cg` | [axil4_slave_wr_mon](../monitor/axil4_slave_wr_mon.md) | Clock-gated write slave + monitor |

The four `*_mon_cg` modules live in `rtl/amba/monitor/`; the four plain
`*_cg` modules live in `rtl/amba/axil4/`.

### Key Features

- ✅ **Dynamic Clock Gating:** Automatic clock disable during idle
- ✅ **Configurable Idle Threshold:** Programmable idle count before gating
- ✅ **Full Functional Equivalence:** Identical to base modules
- ✅ **Status Monitoring:** `cg_gating` and `cg_idle` status outputs
- ✅ **Runtime Bypass:** `cfg_cg_enable = 0` disables gating entirely

There is **no scan/test-mode bypass port**. `clock_gate_ctrl` exposes only
`cfg_cg_enable`; a DFT flow must drive that low (or bypass the ICG cell in the
scan-insertion step) to hold the clock free-running during scan.

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
| `cg_idle` | Output | 1 | No activity was seen on the previous cycle (registered `~wakeup`) |

**All other ports are identical to the base module, with one exception:** the
base module's `busy` output is **not** brought out on the `_cg` wrapper. It is
consumed internally as one of the wakeup terms. Use `cg_idle` (or `cg_gating`)
for interface idle detection on a `_cg` module.

There is no cumulative gated-cycle counter on these modules. If you need one,
count `cg_gating` in the surrounding logic on the ungated clock.

---

## Usage Example

```systemverilog
axil4_master_rd_cg #(
    // Base parameters
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32),
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(4),

    // Clock gating
    .CG_IDLE_COUNT_WIDTH(4)  // Up to 15 idle cycles
) u_axil_rd_cg (
    .aclk(axi_clk),
    .aresetn(axi_resetn),

    // Clock gating configuration
    .cfg_cg_enable(1'b1),         // Enable gating
    .cfg_cg_idle_count(4'd5),     // Gate after 5 idle cycles

    // AXIL signals (identical to base module)
    .fub_araddr(cpu_araddr),
    // ... rest of AR/R signals ...

    // Clock gating status
    .cg_gating(rd_clk_gated),
    .cg_idle(rd_idle)
);
```

---

## Clock Gating Behavior

The `_cg` wrapper builds a wakeup term from the module's channel activity and
the base module's internal `busy`, and hands it to `amba_clock_gate_ctrl`, which
registers it and drives `clock_gate_ctrl` and its ICG cell. For
`axil4_master_rd_cg` the terms are:

```systemverilog
assign user_valid = fub_arvalid || fub_rready || int_busy;
assign axi_valid  = m_axil_arvalid || m_axil_rvalid;
```

**Gating Conditions (All Must Be True):**
1. No activity in `user_valid` or `axi_valid`
2. Idle for `cfg_cg_idle_count` consecutive cycles (the idle counter counts down
   to 0 and holds)
3. Gating enabled (`cfg_cg_enable = 1`)

**Ungating Conditions (Any Triggers Ungating):**
1. Any `*valid` signal asserted on either side of the module
2. `fub_rready` asserted, or the base module still `busy`

**Gating latency:** `cfg_cg_idle_count + 1` clocks after the internal wakeup
deasserts, which is `cfg_cg_idle_count + 2` clocks after the last bus activity
on AXI4-Lite (one extra for the `r_wakeup` flop).

**Ungating latency:** activity is registered once (AXI4, AXI5, AXI4-Lite,
AXI4-Stream) or twice (APB, APB5, AXI5-Stream) before reaching the ICG enable,
which is combinational. The AXIL4 `_cg` wrappers drive `user_valid`/`axi_valid`
combinationally, so there is exactly **1 register stage** — `r_wakeup` inside
`amba_clock_gate_ctrl` — and the first gated-clock rising edge available to the
block arrives **2 clocks** after activity asserts, not 0. Note that
`clock_gate_ctrl` contributes no flop of its own: `w_gate_enable` is
combinational from `wakeup` straight into the ICG enable, so the second clock is
the released edge itself rather than a further register stage. The
wrapper covers this by forcing the module's `ready` outputs low while
`cg_gating` is asserted, for example:

```systemverilog
assign fub_arready   = cg_gating ? 1'b0 : int_arready;
assign m_axil_rready = cg_gating ? 1'b0 : int_rready;
```

so a request presented while gated is simply not accepted until the clock is
running again. No data is lost, but a transaction that arrives into a gated
interface pays the wakeup cost before its first handshake.

---

## Configuration Guidelines

### Idle Count Selection

**Aggressive Gating (Register Access):**
```systemverilog
.cfg_cg_idle_count(4'd1)   // Gate after 1 idle cycle
// AXI4-Lite typical: Burst register access with idle gaps
```

**Moderate Gating (Balanced):**
```systemverilog
.cfg_cg_idle_count(4'd5)   // Gate after 5 idle cycles
// General purpose configuration
```

**Conservative Gating (Low Latency):**
```systemverilog
.cfg_cg_idle_count(4'd10)  // Gate after 10 idle cycles
// Critical control paths, minimal overhead
```

**Disable Gating:**
```systemverilog
.cfg_cg_enable(1'b0)       // Clock gating disabled
// 100% utilization or ultra-low-latency paths
```

### When to Use Clock Gating

**✅ Recommended For:**
- Register access patterns (idle between accesses)
- Low-duty-cycle control interfaces
- Power-constrained systems

**❌ Not Recommended For:**
- 100% utilization scenarios
- Ultra-low-latency critical paths
- Continuous register polling

---

## Power Savings Estimates

### Typical Savings (AXI4-Lite Register Access)

The percentages below are **rough expectations for dynamic clock power in the
gated block only**, relative to the same module with `cfg_cg_enable = 0` at the
same frequency. They are not measured power-analysis results, they exclude
leakage (which gating does not reduce), and they exclude the clock tree upstream
of the ICG cell. Run power analysis on your own target before relying on them.

| Traffic Pattern | Duty Cycle | Idle Count | Est. Dynamic Power Savings |
|-----------------|------------|------------|----------------------------|
| Burst register reads | 20% | 1 | 35-40% |
| Sporadic writes | 10% | 1 | 40-45% |
| Periodic polling | 50% | 5 | 20-25% |
| High activity | 80% | 5 | 5-10% |

**Note:** AXI4-Lite often has better power savings than AXI4 due to:
- Single-beat transactions (more idle gaps)
- Simpler control (faster idle detection)
- Register access patterns (bursty by nature)

---

## Complete Documentation

**For full clock gating details, see:**
- **[AXI4 Clock Gating Guide](../axi4/axi4_clock_gating_guide.md)** - Complete reference with:
  - Detailed gating behavior and state machine
  - Power savings calculations and examples
  - Dynamic configuration patterns
  - Synthesis considerations

**AXIL4-specific notes:**
- Same architecture as AXI4 clock gating
- Typically better power savings (bursty register access)
- Simpler configuration (fewer outstanding transactions)

---

## Related Documentation

### Base Modules
- **[axil4_master_rd](axil4_master_rd.md)** - Base read master
- **[axil4_master_wr](axil4_master_wr.md)** - Base write master
- **[axil4_slave_rd](axil4_slave_rd.md)** - Base read slave
- **[axil4_slave_wr](axil4_slave_wr.md)** - Base write slave
- **[Monitor modules](../monitor/axil4_master_rd_mon.md)** - Base monitor modules

### Architecture
- **[AXI4 Clock Gating Guide](../axi4/axi4_clock_gating_guide.md)** - Complete reference
- **[RTLAmba Overview](../overview.md)** - Complete AMBA subsystem
- **[AXIL4 Index](README.md)** - AXIL4 module index

---

**Last Updated:** 2026-07-19

---

## Navigation

- **[← Back to AXIL4 Index](README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
