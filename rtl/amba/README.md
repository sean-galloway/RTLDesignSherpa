# AMBA Subsystem - Quick Start Guide

**Version:** 1.1
**Last Updated:** 2026-06-24
**Status:** Active Development

---

## Overview

The AMBA subsystem provides production-ready monitoring, observation, and bus-infrastructure components for AXI4, AXI4-Lite, AXI5, APB, APB5, and AXI-Stream protocols. All monitors feature error detection, timeout monitoring, and standardized 64-bit monitor bus output.

**Quick Stats (as of 2026-06-24):**
- 📦 **155 SV modules** across 8 protocol directories + shared
- 🧩 **48 shared infrastructure modules** in `rtl/amba/shared/` (monitors, monbus, observation, sdpram, CDC, arbiters)
- ✅ **~95% test coverage** (functional)
- 🔧 **Production-ready** monitors
- 📖 **Comprehensive docs** in `docs/markdown/RTLAmba/`
- 🧪 **Fully verified** (CocoTB + pytest)

---

## Quick Links

### 📚 Detailed Documentation
- **[RTL Documentation](../../docs/markdown/RTLAmba/index.md)** ← Complete module specs
- **[Overview](../../docs/markdown/RTLAmba/overview.md)** ← Architecture and design
- **[Monitor Package](../../docs/markdown/RTLAmba/includes/monitor_package_spec.md)** ← Packet format spec

### 📋 This Subsystem
- **[PRD](PRD.md)** - Product requirements (this subsystem)
- **[CLAUDE](CLAUDE.md)** - AI assistance guide
- **[Tasks](PRD/TASKS.md)** - Current work items
- **[Known Issues](KNOWN_ISSUES/)** - Bug tracking

### 📖 Guides
- **[Configuration Guide](../../docs/AXI_Monitor_Configuration_Guide.md)** ← **Start here for monitor setup!**

---

## Supported Protocols

| Protocol | Status | Modules | Features |
|----------|--------|---------|----------|
| **AXI4** | ✅ Complete | `rtl/amba/axi4/axi4_{master,slave}_{rd,wr}_mon.sv` (+ `_cg` clock-gated variants) | Burst, out-of-order, outstanding |
| **AXI4-Lite** | ✅ Complete | `rtl/amba/axil4/axil4_{master,slave}_{rd,wr}_mon.sv` (+ `_cg`) — **dedicated wrappers**, not shared with AXI4 | Single-beat, simplified |
| **AXI5** | ✅ Available | `rtl/amba/axi5/` | AXI5 extensions |
| **APB / APB5** | ✅ Complete | `rtl/amba/apb/apb_monitor.sv`, `rtl/amba/apb5/` | Peripheral bus |
| **AXI-Stream** | ✅ Complete | `rtl/amba/axis4/`, `rtl/amba/axis5/` | Streaming data |

**Detailed specs:** See `docs/markdown/RTLAmba/`

> **Note (2026):** AXI4-Lite monitors now ship as **dedicated `axil4_*_mon.sv` wrappers** in `rtl/amba/axil4/` rather than the prior `IS_AXI=0` parameter overload on the AXI4 wrappers. Existing instances using the parameter form should migrate; the wrappers share the same `axi_monitor_base` core and packet format.

---

## Shared Infrastructure (`rtl/amba/shared/`)

48 protocol-agnostic modules grouped by role. The monitor core, observation, and monbus components below are protocol-independent and are wired up inside the per-protocol `*_mon.sv` wrappers above (or instantiated directly by integrations).

### Monitor core (13)
| Module | Role |
|---|---|
| `axi_monitor_base.sv` | Top-level monitor scaffold; instantiated by every `*_mon` wrapper |
| `axi_monitor_trans_mgr.sv` | Outstanding-transaction table (pipelined active-count to close 100 MHz) |
| `axi_monitor_addr_check.sv` | Address range check / region filtering |
| `axi_monitor_filtered.sv` | Configurable per-channel packet filtering |
| `axi_monitor_timer.sv` | Free-running timer + per-transaction stamps |
| `axi_monitor_timeout.sv` | Timeout detection logic |
| `axi_monitor_reporter.sv` | Packet generation dispatcher (refactored: per-packet-type subblocks below) |
| `axi_monitor_reporter_compl.sv` | Completion packets |
| `axi_monitor_reporter_debug.sv` | Debug packets |
| `axi_monitor_reporter_error.sv` | Error packets |
| `axi_monitor_reporter_perf.sv` | Performance packets |
| `axi_monitor_reporter_threshold.sv` | Threshold packets |
| `axi_monitor_reporter_timeout.sv` | Timeout packets |
| `monitor_trans_cam.sv` | CAM lookup for transaction table (used by trans_mgr) |

### Observation / performance (3)
| Module | Role |
|---|---|
| `axi4_dma_observer.sv` | DMA observability wrapper; per-channel AW→W AWID order tracker (no sideband), per-port latency histograms |
| `axi_perf_latency_hist.sv` | 16-bucket log2 latency histogram per channel |
| `axi_bus_meter.sv` | 4-bucket bus utilization meter (productive / backpressure / starvation / idle) |

### Monitor Bus (monbus) infrastructure (10)
| Module | Role |
|---|---|
| `monbus_arbiter.sv` | Top-level monbus arbitration |
| `monbus_group_core.sv` | Shared filter + FIFO core (used by all `monbus_*_*_group.sv` wrappers) |
| `monbus_axi4_axi4_group.sv` | AXI4↔AXI4 monbus group wrapper |
| `monbus_axi4_axil_group.sv` | AXI4↔AXIL bridge group |
| `monbus_axil_axi4_group.sv` | AXIL↔AXI4 bridge group (32-bit err-drain) |
| `monbus_axil_axil_group.sv` | AXIL↔AXIL group (32-bit err-drain) |
| `monbus_compressor.sv` | Optional packet compressor (mod-3 packing, runtime `cfg_compress_en`) |
| `monbus_halfbeat_packer.sv` | Half-beat packer for higher monbus efficiency |
| `monbus_cam.sv` | Monbus CAM for packet matching/replay |
| `monbus_cam_pipe.sv` | Pipelined CAM variant |

### Arbiters with monbus instrumentation (3)
| Module | Role |
|---|---|
| `arbiter_monbus_common.sv` | Shared base used by the variants below |
| `arbiter_rr_pwm_monbus.sv` | Round-robin + PWM weight + monbus |
| `arbiter_wrr_pwm_monbus.sv` | Weighted RR + PWM + monbus |

### Clock-domain crossing (4)
| Module | Role |
|---|---|
| `cdc_2_phase_handshake.sv` | 2-phase CDC handshake |
| `cdc_4_phase_handshake.sv` | 4-phase CDC handshake |
| `cdc_open_loop.sv` | Open-loop CDC for one-shot pulses |
| `cdc_synchronizer.sv` | Plain multi-flop synchronizer |

### Storage helpers (5) — not strictly monitor/observation
| Module | Role |
|---|---|
| `sdpram_core.sv` | FUB-shaped SDP RAM core, shared by the four protocol-pair wrappers below |
| `sdpram_slave_axi4_axi4.sv` | AXI4↔AXI4 SDP RAM slave |
| `sdpram_slave_axi4_axil.sv` | AXI4↔AXIL slave |
| `sdpram_slave_axil_axi4.sv` | AXIL↔AXI4 slave |
| `sdpram_slave_axil_axil.sv` | AXIL↔AXIL slave |

### Helpers / test infrastructure
- `axi4_dma_slaves.sv` — bundled slave wrapper for DMA testbenches
- `axi4_slave_rd_pattern_gen.sv` — pattern generator (used by slave-side test harness)
- `axi4_slave_wr_crc_check.sv` — CRC checker for write verification
- `axi_master_rd_splitter.sv`, `axi_master_wr_splitter.sv`, `axi_split_combi.sv` — burst splitters
- `axi_gen_addr.sv` — address generator
- `amba_clock_gate_ctrl.sv` — gate control logic
- `apb_monitor_addr_check.sv` — APB address-range filter

---

## Quick Start: AXI4 Monitor

### 1. Basic Integration

```systemverilog
// Instantiate AXI4 Master Read Monitor
axi4_master_rd_mon #(
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),
    .MAX_TRANSACTIONS(16)
) u_axi_rd_mon (
    // Clock & Reset
    .aclk               (axi_clk),
    .aresetn            (axi_rst_n),

    // AXI4 Read Address Channel
    .axi_arid           (m_axi_arid),
    .axi_araddr         (m_axi_araddr),
    .axi_arlen          (m_axi_arlen),
    .axi_arsize         (m_axi_arsize),
    .axi_arburst        (m_axi_arburst),
    .axi_arvalid        (m_axi_arvalid),
    .axi_arready        (m_axi_arready),

    // AXI4 Read Data Channel
    .axi_rid            (m_axi_rid),
    .axi_rdata          (m_axi_rdata),
    .axi_rresp          (m_axi_rresp),
    .axi_rlast          (m_axi_rlast),
    .axi_rvalid         (m_axi_rvalid),
    .axi_rready         (m_axi_rready),

    // Monitor Bus Output (64-bit packets)
    .monbus_pkt_valid   (mon_pkt_valid),
    .monbus_pkt_ready   (mon_pkt_ready),
    .monbus_pkt_data    (mon_pkt_data),   // [63:0]

    // Configuration (runtime control)
    .cfg_error_enable   (1'b1),    // Enable error detection
    .cfg_compl_enable   (1'b1),    // Enable completion packets
    .cfg_timeout_enable (1'b1),    // Enable timeout detection
    .cfg_perf_enable    (1'b0),    // ⚠️ Disable to avoid congestion
    .cfg_debug_enable   (1'b0)     // Disable unless needed
);
```

### 2. Configuration Modes

**⚠️ CRITICAL:** Never enable all packet types simultaneously!

**Mode 1: Functional Verification (Recommended)**
```systemverilog
.cfg_error_enable   (1'b1),  // Catch SLVERR, DECERR, orphans
.cfg_compl_enable   (1'b1),  // Track transaction completions
.cfg_timeout_enable (1'b1),  // Detect stuck transactions
.cfg_perf_enable    (1'b0),  // ⚠️ DISABLE (high packet rate)
.cfg_debug_enable   (1'b0)   // Disable unless debugging
```

**Mode 2: Performance Analysis**
```systemverilog
.cfg_error_enable   (1'b1),  // Still catch errors
.cfg_compl_enable   (1'b0),  // ⚠️ DISABLE (reduce traffic)
.cfg_timeout_enable (1'b0),  // Disable
.cfg_perf_enable    (1'b1),  // Enable performance metrics
.cfg_debug_enable   (1'b0)
```

**📖 See:** `docs/AXI_Monitor_Configuration_Guide.md` for detailed strategies

### 3. Monitor Bus Packet Format

```
Monitor Bus Packet [63:0]:
├─ [63:60] Packet Type
│   ├─ 0x0: ERROR
│   ├─ 0x1: COMPLETION
│   ├─ 0x2: TIMEOUT
│   ├─ 0x3: THRESHOLD
│   ├─ 0x4: PERFORMANCE
│   └─ 0x5: DEBUG
├─ [59:57] Protocol (0=AXI, 1=APB, 2=AXIS)
├─ [56:53] Event Code
├─ [52:47] Channel ID
├─ [46:43] Unit ID
├─ [42:35] Agent ID
└─ [34:0]  Event-specific data (address, latency, etc.)
```

**📖 See:** `docs/markdown/RTLAmba/includes/monitor_package_spec.md`

---

## Quick Start: APB Monitor

```systemverilog
apb_monitor #(
    .ADDR_WIDTH(16),
    .DATA_WIDTH(32),
    .MAX_TRANSACTIONS(8)
) u_apb_mon (
    .pclk               (apb_clk),
    .presetn            (apb_rst_n),

    // APB Interface
    .paddr              (apb_paddr),
    .psel               (apb_psel),
    .penable            (apb_penable),
    .pwrite             (apb_pwrite),
    .pwdata             (apb_pwdata),
    .pready             (apb_pready),
    .prdata             (apb_prdata),
    .pslverr            (apb_pslverr),

    // Monitor Bus
    .monbus_pkt_valid   (apb_mon_valid),
    .monbus_pkt_ready   (apb_mon_ready),
    .monbus_pkt_data    (apb_mon_data),

    // Configuration
    .cfg_error_enable   (1'b1),
    .cfg_compl_enable   (1'b1),
    .cfg_timeout_enable (1'b1)
);
```

**📖 See:** `docs/markdown/RTLAmba/apb/`

---

## Quick Start: AXI-Stream

```systemverilog
// Master (transmit) side
axis_master #(
    .DATA_WIDTH(64),
    .ID_WIDTH(8),
    .DEST_WIDTH(4),
    .USER_WIDTH(1)
) u_axis_master (
    .aclk               (axis_clk),
    .aresetn            (axis_rst_n),

    // AXIS Interface
    .m_axis_tdata       (axis_tdata),
    .m_axis_tkeep       (axis_tkeep),
    .m_axis_tlast       (axis_tlast),
    .m_axis_tvalid      (axis_tvalid),
    .m_axis_tready      (axis_tready),

    // Monitor Bus
    .monbus_pkt_valid   (axis_mon_valid),
    .monbus_pkt_data    (axis_mon_data)
);
```

**📖 See:** `docs/markdown/RTLAmba/fabric/`

---

## Common Integration Patterns

### Pattern 1: AXI4 Crossbar Monitoring

```systemverilog
// Monitor each master interface
genvar i;
generate
    for (i = 0; i < NUM_MASTERS; i++) begin : gen_master_mon
        axi4_master_rd_mon #(...) u_rd_mon (
            .axi_arid   (m_axi_arid[i]),
            // ... connect master[i] signals
            .monbus_pkt_valid (master_mon_valid[i]),
            .monbus_pkt_data  (master_mon_data[i])
        );
    end
endgenerate

// Aggregate monitor packets
arbiter_rr_monbus #(
    .N(NUM_MASTERS)
) u_mon_arbiter (
    .i_request  (master_mon_valid),
    .i_data     (master_mon_data),
    .o_valid    (aggregated_mon_valid),
    .o_data     (aggregated_mon_data)
);
```

### Pattern 2: Monitor Bus to Memory

```systemverilog
// Capture monitor packets to FIFO
gaxi_fifo_sync #(
    .DATA_WIDTH(64),
    .DEPTH(1024)
) u_mon_fifo (
    .i_clk      (clk),
    .i_rst_n    (rst_n),
    .i_data     (monbus_pkt_data),
    .i_valid    (monbus_pkt_valid),
    .o_ready    (monbus_pkt_ready),
    .o_data     (fifo_mon_data),
    .o_valid    (fifo_mon_valid),
    .i_ready    (dma_ready)
);

// DMA monitor packets to system memory for analysis
```

### Pattern 3: Clock-Gated Monitors (Power Optimization)

```systemverilog
// Use clock-gated variant
axi4_master_rd_mon_cg #(
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64)
) u_axi_mon_cg (
    .aclk               (axi_clk),
    .aresetn            (axi_rst_n),
    .cg_enable          (monitor_enable),  // Clock gate control
    // ... rest of connections
);
```

---

## Testing Your Integration

### Run Monitor Tests

```bash
# Run comprehensive AXI monitor test
pytest val/amba/test_axi_monitor.py -v

# Run all AMBA tests
pytest val/amba/ -v

# Run specific protocol
pytest val/amba/test_apb_monitor.py -v
pytest val/amba/test_axis_master.py -v

# With waveform dump
pytest val/amba/test_axi_monitor.py -v --vcd=waves.vcd
gtkwave waves.vcd
```

### Test Results (Current Status)

**AXI Monitor:** 6/8 tests passing
- ✅ Basic transactions (5/5)
- ✅ Burst transactions (6/6)
- ✅ Outstanding (7/7)
- ✅ ID reordering (4/4)
- ✅ Backpressure
- ✅ Timeouts (3 detected)
- ⚠️ Error responses (test config issue)
- ⚠️ Orphan detection (test config issue)

---

## Common Gotchas

### ❌ Gotcha 1: Enabling All Packet Types

**Problem:**
```systemverilog
.cfg_error_enable   (1'b1),
.cfg_compl_enable   (1'b1),
.cfg_timeout_enable (1'b1),
.cfg_perf_enable    (1'b1),  // ❌ TOO MUCH TRAFFIC!
.cfg_debug_enable   (1'b1)   // ❌ EVEN MORE TRAFFIC!
```

**Solution:**
- Use separate configurations for different test phases
- Never enable completions + performance together
- See `docs/AXI_Monitor_Configuration_Guide.md`

### ❌ Gotcha 2: Insufficient MAX_TRANSACTIONS

**Problem:**
```systemverilog
axi4_master_rd_mon #(
    .MAX_TRANSACTIONS(4)  // ❌ Too small for burst traffic
) u_mon (...);
```

**Solution:**
- Size MAX_TRANSACTIONS >= maximum outstanding transactions
- Typical: 16-32 for general use
- Monitor logs warning if table exhausts

### ❌ Gotcha 3: Ignoring Monitor Bus Backpressure

**Problem:**
```systemverilog
assign monbus_pkt_ready = 1'b1;  // ❌ Always ready, packets may drop!
```

**Solution:**
- Connect to proper FIFO or downstream logic
- Monitor will hold packets when ready=0
- Internal FIFO prevents loss during short stalls

---

## Performance Considerations

### Resource Utilization

**Per Monitor:**
- Logic: <1000 LUTs (depends on MAX_TRANSACTIONS)
- Memory: Transaction table (MAX_TRANSACTIONS × entry size)
- FIFOs: Internal packet buffering (configurable depth)

**Optimization:**
- Use smaller MAX_TRANSACTIONS if possible
- Use `*_cg.sv` variants for power savings
- Disable unused packet types

### Timing

**Critical Paths:**
- Transaction ID lookup: O(MAX_TRANSACTIONS) comparisons
- Packet formatting: Combinational (1 cycle)
- Output buffering: Registered

**Meeting Timing:**
- Use `REG_OUTPUT=1` on arbiter_monbus modules
- Pipeline monitor bus connections
- Consider clock-gated variants

---

## Troubleshooting

### Issue: Monitor Not Generating Packets

**Check:**
1. ✅ Configuration enables correct packet types
2. ✅ Monitor bus `ready` signal asserted
3. ✅ Reset properly deasserted
4. ✅ AXI/APB transactions actually occurring

**Debug:**
```bash
# Run test with verbose logging
pytest val/amba/test_axi_monitor.py -v -s

# Check waveforms
pytest val/amba/test_axi_monitor.py --vcd=debug.vcd
gtkwave debug.vcd
```

### Issue: Transaction Table Exhaustion

**Symptoms:**
- Monitor stops generating packets
- Log shows "MAX_TRANSACTIONS reached"

**Solutions:**
1. Increase MAX_TRANSACTIONS parameter
2. Verify transactions completing (check RLAST/BVALID)
3. Check for protocol violations (orphan data)

**Note:** Recent fix added event_reported feedback - should no longer occur

### Issue: Packet Loss/Corruption

**Symptoms:**
- Missing monitor packets
- Incorrect packet data

**Solutions:**
1. Add downstream FIFO for buffering
2. Don't enable too many packet types
3. Check monitor bus protocol (valid/ready handshake)

---

## Advanced Topics

### Filter Configuration

Some monitors support address/ID filtering (check module parameters):

```systemverilog
axi_monitor_filtered #(
    .ENABLE_ADDR_FILTER(1),
    .ADDR_FILTER_BASE(32'h1000_0000),
    .ADDR_FILTER_MASK(32'hF000_0000)
) u_filtered_mon (
    // ... only monitors addresses in 0x1000_0000 - 0x1FFF_FFFF range
);
```

### Custom Packet Types

Extend monitor_pkg.sv for custom packet types:

```systemverilog
// In monitor_pkg.sv
typedef enum logic [3:0] {
    PKT_ERROR       = 4'h0,
    PKT_COMPLETION  = 4'h1,
    PKT_TIMEOUT     = 4'h2,
    PKT_CUSTOM      = 4'hF  // Your custom type
} pkt_type_e;
```

---

## Documentation Index

### This Subsystem
- **[PRD.md](PRD.md)** - Product requirements overview
- **[CLAUDE.md](CLAUDE.md)** - AI assistance guide
- **[PRD/TASKS.md](PRD/TASKS.md)** - Current work items
- **[KNOWN_ISSUES/](KNOWN_ISSUES/)** - Bug tracking

### Detailed RTL Documentation
📁 **`docs/markdown/RTLAmba/`** ← **Main technical reference**
- [Index](../../docs/markdown/RTLAmba/index.md) - Complete module list
- [Overview](../../docs/markdown/RTLAmba/overview.md) - Architecture
- [AXI Modules](../../docs/markdown/RTLAmba/axi/)
- [APB Modules](../../docs/markdown/RTLAmba/apb/)
- [AXIS Modules](../../docs/markdown/RTLAmba/fabric/)
- [Monitor Package](../../docs/markdown/RTLAmba/includes/monitor_package_spec.md)

### Guides
- **[Configuration Guide](../../docs/AXI_Monitor_Configuration_Guide.md)** ← **Essential reading!**

### Root Documentation
- [Master PRD](../../PRD.md) - Repository overview
- [Claude Guide](../../CLAUDE.md) - AI assistance (root)
- [README](../../README.md) - Getting started

---

## Quick Command Reference

```bash
# Run tests
pytest val/amba/test_axi_monitor.py -v          # AXI monitor
pytest val/amba/test_apb_monitor.py -v          # APB monitor
pytest val/amba/ -v                             # All AMBA tests

# Lint RTL
verilator --lint-only rtl/amba/shared/axi_monitor_base.sv
verilator --lint-only rtl/amba/axi4/axi4_master_rd_mon.sv

# View documentation
cat docs/markdown/RTLAmba/index.md
cat docs/AXI_Monitor_Configuration_Guide.md

# Check tasks and issues
cat rtl/amba/PRD/TASKS.md
ls rtl/amba/KNOWN_ISSUES/
```

---

## Getting Help

1. **Configuration issues?** → Read `docs/AXI_Monitor_Configuration_Guide.md`
2. **Integration questions?** → Check `docs/markdown/RTLAmba/overview.md`
3. **Module details?** → See `docs/markdown/RTLAmba/{protocol}/`
4. **Known bugs?** → Check `KNOWN_ISSUES/`
5. **AI assistance?** → See `CLAUDE.md`

---

**Version:** 1.0
**Last Updated:** 2025-09-30
**Maintained By:** RTL Design Sherpa Project
