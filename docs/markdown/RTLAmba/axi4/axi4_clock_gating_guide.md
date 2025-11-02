# AXI4 Clock-Gated Variants Guide

**Location:** `rtl/amba/axi4/*_cg.sv`
**Status:** ✅ Production Ready

---

## Overview

All AXI4 modules in this subsystem have clock-gated (`_cg`) variants that add power management capabilities through dynamic clock gating. These modules automatically gate the clock when interfaces are idle for a configurable period, reducing dynamic power consumption in low-activity scenarios.

### Available Clock-Gated Modules

| Module | Base Module | Description |
|--------|-------------|-------------|
| `axi4_master_rd_cg` | [axi4_master_rd](axi4_master_rd.md) | Clock-gated read master |
| `axi4_master_wr_cg` | [axi4_master_wr](axi4_master_wr.md) | Clock-gated write master |
| `axi4_slave_rd_cg` | [axi4_slave_rd](axi4_slave_rd.md) | Clock-gated read slave |
| `axi4_slave_wr_cg` | [axi4_slave_wr](axi4_slave_wr.md) | Clock-gated write slave |
| `axi4_master_rd_mon_cg` | [axi4_master_rd_mon](axi4_master_rd_mon.md) | Clock-gated read master with monitoring |
| `axi4_master_wr_mon_cg` | [axi4_master_wr_mon](axi4_master_wr_mon.md) | Clock-gated write master with monitoring |
| `axi4_slave_rd_mon_cg` | [axi4_slave_rd_mon](axi4_slave_rd_mon.md) | Clock-gated read slave with monitoring |
| `axi4_slave_wr_mon_cg` | [axi4_slave_wr_mon](axi4_slave_wr_mon.md) | Clock-gated write slave with monitoring |

### Key Features

- ✅ **Dynamic Clock Gating:** Automatic clock disable during idle periods
- ✅ **Configurable Idle Threshold:** Programmable idle count before gating
- ✅ **Full Functional Equivalence:** Identical functionality to base modules
- ✅ **Status Monitoring:** Real-time gating status and cumulative clock count
- ✅ **Test Mode Support:** Bypass capability for scan testing
- ✅ **Zero Performance Impact:** Immediate ungating on activity

---

## Additional Parameters (All _cg Modules)

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | int | 4 | Width of idle counter (max idle = 2^N-1 cycles) |

**All other parameters are identical to the base module.**

---

## Additional Ports (All _cg Modules)

### Clock Gating Configuration Inputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_cg_enable` | Input | 1 | Enable clock gating (0=disabled, 1=enabled) |
| `cfg_cg_idle_count` | Input | CG_IDLE_COUNT_WIDTH | Idle cycles before gating (0=immediate gating) |

### Clock Gating Status Outputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cg_gating` | Output | 1 | Clock currently gated (1=gated, 0=running) |
| `cg_clk_count` | Output | 32 | Cumulative gated clock cycles (power metric) |

**All other ports are identical to the base module.**

---

## Clock Gating Behavior

### Gating Conditions (All Must Be True)

1. **Interface Idle:** No valid/ready handshakes on any AXI channel
2. **Idle Duration:** Idle for ≥ `cfg_cg_idle_count` consecutive cycles
3. **Gating Enabled:** `cfg_cg_enable = 1`

### Ungating Conditions (Any Triggers Immediate Ungating)

1. Any `*valid` signal asserted on any channel
2. Configuration change (`cfg_cg_enable` or `cfg_cg_idle_count`)

**Ungating Latency:** 0 cycles (immediate)

### State Machine

```
┌─────────┐  idle_count < threshold  ┌──────────┐
│ RUNNING │◄─────────────────────────┤  IDLE    │
│         │                          │ Counting │
└────┬────┘                          └─────┬────┘
     │                                     │
     │ activity = 0                        │ count >= threshold
     │ (no valid signals)                  │ && cg_enable
     │                                     │
     │                                     ▼
     │                               ┌──────────┐
     └──────────────────────────────►│  GATED   │
       activity detected              │ (clock   │
       (any valid signal)             │  stopped)│
                                      └──────────┘
```

---

## Usage Examples

### Basic Clock Gating (Master Read)

```systemverilog
axi4_master_rd_cg #(
    // Base parameters
    .SKID_DEPTH_AR      (2),
    .SKID_DEPTH_R       (4),
    .AXI_ID_WIDTH       (4),
    .AXI_ADDR_WIDTH     (32),
    .AXI_DATA_WIDTH     (64),

    // Clock gating parameters
    .CG_IDLE_COUNT_WIDTH(4)   // Up to 15 idle cycles
) u_rd_master_cg (
    .aclk               (axi_clk),
    .aresetn            (axi_resetn),

    // Clock gating configuration
    .cfg_cg_enable      (1'b1),      // Enable gating
    .cfg_cg_idle_count  (4'd5),      // Gate after 5 idle cycles

    // AXI signals (identical to base module)
    .fub_axi_arid       (cpu_arid),
    .fub_axi_araddr     (cpu_araddr),
    // ... rest of AR/R signals ...

    .m_axi_arid         (mem_arid),
    .m_axi_araddr       (mem_araddr),
    // ... rest of AR/R signals ...

    // Clock gating status
    .cg_gating          (rd_clk_gated),
    .cg_clk_count       (rd_gated_cycles)
);

// Monitor power savings
always_ff @(posedge axi_clk) begin
    if (rd_clk_gated) begin
        $display("Read master clock gated - saving power");
    end
end
```

### Dynamic Configuration (Runtime Adjustment)

```systemverilog
// Power management controller
logic [3:0] idle_threshold;

always_comb begin
    case (power_mode)
        POWER_HIGH_PERF:  idle_threshold = 4'd15;  // Conservative gating
        POWER_BALANCED:   idle_threshold = 4'd5;   // Moderate gating
        POWER_LOW:        idle_threshold = 4'd1;   // Aggressive gating
        default:          idle_threshold = 4'd5;
    endcase
end

axi4_master_wr_cg #(
    // ... parameters ...
) u_wr_master_cg (
    // ... ports ...

    // Dynamic clock gating control
    .cfg_cg_enable      (power_mgmt_enable),
    .cfg_cg_idle_count  (idle_threshold),

    .cg_gating          (wr_clk_gated),
    .cg_clk_count       (wr_gated_cycles)
);
```

### System-Level Power Monitoring

```systemverilog
// Aggregate power metrics from all interfaces
wire master_rd_gated, master_wr_gated;
wire slave_rd_gated, slave_wr_gated;

wire [31:0] master_rd_gated_cycles;
wire [31:0] master_wr_gated_cycles;
wire [31:0] slave_rd_gated_cycles;
wire [31:0] slave_wr_gated_cycles;

// Total gated cycles (power savings metric)
wire [31:0] total_gated_cycles = master_rd_gated_cycles +
                                 master_wr_gated_cycles +
                                 slave_rd_gated_cycles +
                                 slave_wr_gated_cycles;

// Instantaneous gating status
wire any_gating = master_rd_gated | master_wr_gated |
                  slave_rd_gated | slave_wr_gated;

// Power savings estimate (assuming 50% power reduction when gated)
wire [31:0] power_savings_percent = (total_gated_cycles * 50) / total_cycles;
```

---

## Configuration Guidelines

### Idle Count Selection

**Aggressive Gating (High Idle Time):**
```systemverilog
.cfg_cg_idle_count(4'd1)   // Gate after 1 idle cycle
// Use when: Burst traffic, low duty cycle, max power savings
```

**Moderate Gating (Balanced):**
```systemverilog
.cfg_cg_idle_count(4'd5)   // Gate after 5 idle cycles
// Use when: Mixed traffic, balanced power/performance
```

**Conservative Gating (Low Latency):**
```systemverilog
.cfg_cg_idle_count(4'd10)  // Gate after 10 idle cycles
// Use when: High throughput, latency-sensitive, minimal power overhead
```

**Disable Gating:**
```systemverilog
.cfg_cg_enable(1'b0)       // Clock gating disabled
// Use when: 100% utilization, ultra-low latency, debug/test
```

### When to Use Clock Gating

**✅ Recommended For:**
- Burst traffic patterns (idle periods between bursts)
- Low-duty-cycle interfaces (< 50% utilization)
- Power-constrained systems (battery, thermal limits)
- Variable workloads (idle states common)

**❌ Not Recommended For:**
- 100% utilization scenarios (no idle time = no power benefit)
- Ultra-low-latency requirements (gating overhead unacceptable)
- Continuous streaming (no natural idle points)

### Traffic Pattern Analysis

**Burst Traffic (Good for Clock Gating):**
```
Time:    |----BURST----|idle|----BURST----|idle|----BURST----|
Gating:  |             |GG|               |GG|               |
Savings: ~30-40% depending on burst duty cycle
```

**Continuous Traffic (Poor for Clock Gating):**
```
Time:    |----DATA----DATA----DATA----DATA----DATA----|
Gating:  |                                             |
Savings: ~0% (never idle long enough to gate)
```

---

## Power Savings Estimates

### Typical Power Savings

| Traffic Pattern | Duty Cycle | Idle Count | Power Savings |
|-----------------|------------|------------|---------------|
| Burst (aggressive) | 30% | 1 | 35-40% |
| Burst (moderate) | 30% | 5 | 30-35% |
| Burst (conservative) | 30% | 10 | 25-30% |
| Mixed workload | 50% | 5 | 20-25% |
| Low activity | 10% | 1 | 40-45% |
| High activity | 80% | 5 | 5-10% |
| Continuous | 100% | any | 0% |

**Note:** Actual savings depend on:
- Process technology (clock tree power)
- Traffic patterns (idle duration distribution)
- Configuration (idle count threshold)
- Logic behind clock gate (amount of logic gated)

### Measuring Power Savings

```systemverilog
// Calculate power savings percentage
logic [31:0] total_cycles;
logic [31:0] gated_cycles;

always_ff @(posedge axi_clk or negedge aresetn) begin
    if (!aresetn) begin
        total_cycles <= '0;
        gated_cycles <= '0;
    end else begin
        total_cycles <= total_cycles + 1;
        if (cg_gating) begin
            gated_cycles <= gated_cycles + 1;
        end
    end
end

// Power savings = (gated_cycles / total_cycles) × 100%
assign power_savings_pct = (gated_cycles * 100) / total_cycles;
```

---

## Design Notes

### Test Mode Support

For scan testing, disable clock gating:
```systemverilog
.cfg_cg_enable(~scan_mode)  // Disable during DFT scan
```

### Simulation Considerations

**Waveform Analysis:**
- `cg_gating=1`: Clock gated (idle)
- `cg_gating=0`: Clock running (active)

**Power Estimation:**
```systemverilog
initial begin
    $monitor("Time %0t: Gating=%b, GatedCycles=%0d",
             $time, cg_gating, cg_clk_count);
end
```

### Synthesis Considerations

**Clock Gating Cell:**
- Uses standard cell library clock gate (GTECH_AND, ICG, etc.)
- Synthesis tool automatically inserts appropriate cell
- No vendor-specific primitives required

**Timing:**
- Clock gating logic adds minimal delay
- Ungating path is critical (0-cycle requirement)
- Gating path is non-critical

---

## Performance Impact

### Latency Analysis

**Ungating Latency:** 0 cycles (immediate)
```
Cycle N:   Interface idle, clock gated
Cycle N+1: ARVALID asserted → clock immediately ungated
Cycle N+1: Transaction proceeds normally
```

**No Performance Penalty:**
- Clock ungates same cycle as activity
- AXI handshake proceeds without delay
- Functionally equivalent to non-gated module

### Throughput

**Sustained Throughput:** Identical to base module
- Gating only occurs during idle
- Active transactions unaffected

---

## Related Documentation

### Base Module Documentation
- **[axi4_master_rd](axi4_master_rd.md)** - Base read master
- **[axi4_master_wr](axi4_master_wr.md)** - Base write master
- **[axi4_slave_rd](axi4_slave_rd.md)** - Base read slave
- **[axi4_slave_wr](axi4_slave_wr.md)** - Base write slave
- **[axi4_master_rd_mon](axi4_master_rd_mon.md)** - Base master read monitor
- **[axi4_master_wr_mon](axi4_master_wr_mon.md)** - Base master write monitor
- **[axi4_slave_rd_mon](axi4_slave_rd_mon.md)** - Base slave read monitor
- **[axi4_slave_wr_mon](axi4_slave_wr_mon.md)** - Base slave write monitor

### Architecture
- **[RTLAmba Overview](../overview.md)** - Complete AMBA subsystem
- **[AXI4 Index](README.md)** - AXI4 module index

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to AXI4 Index](README.md)**
- **[← Back to RTLAmba Index](../README.md)**
- **[← Back to Main Documentation Index](../../index.md)**
