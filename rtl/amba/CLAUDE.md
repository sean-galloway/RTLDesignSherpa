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

# Claude Code Guide: AMBA Subsystem

**Version:** 1.0
**Last Updated:** 2025-09-30
**Purpose:** AI-specific guidance for working with rtl/amba/ subsystem

---

## Quick Context

**What:** AMBA protocol monitoring infrastructure (AXI4, AXI4-Lite, APB, AXI-Stream)
**Status:** 🟡 Active development - production-ready monitors, test refinement ongoing
**Your Role:** Help users integrate monitors, configure correctly, debug issues

**📖 Detailed Specs:** `docs/markdown/RTLAmba/` ← **Always reference this for technical details**

---

## 📖 Global Requirements Reference

**IMPORTANT: Check `/GLOBAL_REQUIREMENTS.md` for mandatory verification standards**

All mandatory requirements are consolidated in the global requirements document:
- **See:** `/GLOBAL_REQUIREMENTS.md` - Repository-wide mandatory requirements
- **AMBA Focus:** Three-layer architecture, queue-based verification, 100% success
- **Universal:** TB location, TBBase inheritance, test naming conventions

This CLAUDE.md provides AMBA-specific guidance. Also review:
- Root `/CLAUDE.md` - Repository-wide patterns
- `docs/markdown/TBClasses/tbclasses_index.md` - Framework usage patterns (full framework lives in the RTLDesignSherpa-DV repo)
- `docs/user-guides/VERIFICATION_ARCHITECTURE_GUIDE.md` - Complete verification patterns

---

## Critical Rules for This Subsystem

### Rule #0: Verification Architecture (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Sections 2.1, 2.3, 2.4 for complete requirements

**AMBA-Specific Structure:**

```
bin/TBClasses/
├── axi4/
│   └── axi4_master_read_tb.py      # AXI4 master read TB
├── axi_monitor/
│   └── axi_monitor_tb.py           # AXI monitor TB
├── apb_monitor/
│   └── apb_monitor_core_tb.py      # APB monitor TB
└── [protocol]/[module]_tb.py

val/amba/
└── test_*.py                        # Test runners (import TBs from framework)
```

**AMBA Import Pattern:**
```python
# val/amba/test_axi4_master_rd.py
from TBClasses.axi4.axi4_master_read_tb import AXI4MasterReadTB

@cocotb.test()
async def axi4_test(dut):
    tb = AXI4MasterReadTB(dut)
    await tb.setup_clocks_and_reset()
    # ... test logic
```

**AMBA Three-Layer Pattern:**
1. **TB Class:** `bin/TBClasses/{protocol}/` - Infrastructure + BFMs
2. **Scoreboard:** `bin/TBClasses/scoreboards/` - Verification logic
3. **Test Runner:** `val/amba/` - Test intelligence

**Verification Method Selection for AMBA:**
- ✅ **Queue Access:** APB monitors, simple control paths, in-order transactions
- ✅ **Memory Models:** Multi-master AXI, out-of-order scenarios, data integrity

**📖 Complete Guide:** `docs/user-guides/VERIFICATION_ARCHITECTURE_GUIDE.md` with AMBA examples

---

### Rule #1: Always Reference Detailed Documentation

**This subsystem has extensive documentation in** `docs/markdown/RTLAmba/`

**Before answering technical questions:**
```bash
# Check detailed docs first
ls docs/markdown/RTLAmba/
cat docs/markdown/RTLAmba/overview.md
cat docs/markdown/RTLAmba/monitor/axi4_master_rd_mon.md
```

**Your answer should:**
1. Provide direct answer/code
2. **Then link to detailed docs:** "See `docs/markdown/RTLAmba/{file}.md` for complete specification"

### Rule #2: Avoid Enabling All Monitor Packet Types

**This is the #1 integration mistake!** The monitor bus sustains at most
1 packet per 2 cycles (reporter output register), so enabling every
packet class under heavy traffic congests it.

```systemverilog
❌ WRONG (User's code):
.cfg_error_enable   (1'b1),
.cfg_compl_enable   (1'b1),
.cfg_perf_enable    (1'b1),  // ❌ PACKET CONGESTION!
.cfg_debug_enable   (1'b1)   // ❌ EVEN WORSE!

✅ CORRECT (Functional debug mode):
.cfg_error_enable   (1'b1),
.cfg_compl_enable   (1'b1),
.cfg_timeout_enable (1'b1),
.cfg_perf_enable    (1'b0),  // ← Disabled
.cfg_debug_enable   (1'b0)   // ← Disabled
```

**Runtime-disable semantics (since `95c9490a`):** a class disabled at
runtime (`cfg_*_enable = 0` with its `ENABLE_*_LOGIC` compiled in) is safe
— its terminal transaction-table entries auto-retire WITHOUT emitting
packets or bumping counters, so the table never leaks and `block_ready`
never wedges. (Before that commit, `cfg_compl_enable=0` with
`ENABLE_COMPL_LOGIC=1` — the documented "performance mode" — leaked every
completed entry and wedged the monitored bus after ~13 transactions.)
Toggling an enable mid-flight may drop that one entry's packet; it can
never leak the slot. If you want to keep marking/counting while
suppressing emission, use `cfg_axi_pkt_mask` (drop mask, 1 = drop, in
`axi_monitor_filtered`) instead of the runtime disable.

**Always link:** "See `docs/user-guides/AXI_Monitor_Configuration_Guide.md` for configuration strategies"

### Rule #3: Know the Known Issues

**Current Status (as of `95c9490a`):**
- ✅ Event reported feedback bug FIXED (2025-09-30)
- ✅ Multi-channel saturation wedge FIXED (`cb29e226`)
- ✅ Runtime-disable leak / same-cycle AW+W / wrapper API / AXI5 W wiring FIXED (`95c9490a`)
- ✅ val/amba regression fully green (679 passed / 0 failed); monitor formal 10/10
- ⚠️ Open (non-monitor): 8-channel STREAM engine wedge (params 7/9/11 family)
- ⚠️ Open (framework): axil4 monitor TB drain-window race — seeds pinned; proper fix in RDS-DV

**Always check:** `rtl/amba/KNOWN_ISSUES/` before diagnosing bugs

```bash
ls rtl/amba/KNOWN_ISSUES/
cat rtl/amba/KNOWN_ISSUES/README.md
```

### Rule #4: Integration = Configuration + Wiring + Downstream

**Complete integration requires:**
1. ✅ Module instantiation with correct parameters
2. ✅ Configuration signals (cfg_*_enable)
3. ✅ **Downstream monitor bus handling** (FIFO, arbiter, or consumer)

**Incomplete example:**
```systemverilog
❌ INCOMPLETE:
axi4_master_rd_mon u_mon (
    // ... AXI signals ...
    .monbus_valid (mon_valid),
    .monbus_packet  (mon_data),
    .monbus_ready (1'b1)  // ❌ Always ready = packet loss risk!
);
```

**Complete example:**
```systemverilog
✅ COMPLETE:
// Monitor
axi4_master_rd_mon u_mon (
    // ... AXI signals ...
    .monbus_valid (mon_valid),
    .monbus_packet  (mon_data),
    .monbus_ready (fifo_ready)
);

// Downstream FIFO
gaxi_fifo_sync #(.DATA_WIDTH(128), .DEPTH(256)) u_fifo (
    .i_valid (mon_valid),
    .i_data  (mon_data),
    .o_ready (fifo_ready),
    // ... connect to consumer
);
```

---

## Module Quick Reference

### AXI4 Monitors

| Module | Purpose | Key Params | Documentation |
|--------|---------|------------|---------------|
| `axi4_master_rd_mon.sv` | Master read monitoring | ID_WIDTH, ADDR_WIDTH, DATA_WIDTH, MAX_TRANSACTIONS | `docs/markdown/RTLAmba/monitor/axi4_master_rd_mon.md` |
| `axi4_master_wr_mon.sv` | Master write monitoring | Same | `docs/markdown/RTLAmba/monitor/` |
| `axi4_slave_rd_mon.sv` | Slave read monitoring | Same | `docs/markdown/RTLAmba/monitor/` |
| `axi4_slave_wr_mon.sv` | Slave write monitoring | Same | `docs/markdown/RTLAmba/monitor/` |
| `*_cg.sv` variants | Clock-gated versions | Same + CG_ENABLE | Power optimization |

### APB Monitors

| Module | Purpose | Key Params | Documentation |
|--------|---------|------------|---------------|
| `apb_monitor.sv` | APB transaction monitoring | ADDR_WIDTH, DATA_WIDTH, MAX_TRANSACTIONS | `docs/markdown/RTLAmba/apb/` |

### AXIS Monitors

| Module | Purpose | Key Params | Documentation |
|--------|---------|------------|---------------|
| `axis_master.sv` | AXIS transmit monitoring | DATA_WIDTH, ID_WIDTH, DEST_WIDTH | `docs/markdown/RTLAmba/axis4/axis_master.md` |
| `axis_slave.sv` | AXIS receive monitoring | Same | `docs/markdown/RTLAmba/axis4/` |

### AXI4-Lite Monitors

| Module | Purpose | Key Params | Documentation |
|--------|---------|------------|---------------|
| `axil4_master_rd_mon.sv` | AXIL master read monitoring | ADDR_WIDTH, DATA_WIDTH, MAX_TRANSACTIONS | `rtl/amba/axil4/` |
| `axil4_master_wr_mon.sv` | AXIL master write monitoring | Same | `rtl/amba/axil4/` |
| `axil4_slave_rd_mon.sv` | AXIL slave read monitoring | Same | `rtl/amba/axil4/` |
| `axil4_slave_wr_mon.sv` | AXIL slave write monitoring | Same | `rtl/amba/axil4/` |
| `*_cg.sv` variants | Clock-gated AXIL versions | Same + CG_ENABLE | Power optimization |

> Dedicated AXIL4 wrappers (not the old `IS_AXI=0` parameter overload). Share `axi_monitor_base` and packet format with the AXI4 wrappers.

### Supporting Infrastructure — `rtl/amba/monitor/` + `rtl/amba/shared/`

All protocol-agnostic. The monitor core, monbus infrastructure, monbus arbiters, and ALL `*_mon` wrappers live in `rtl/amba/monitor/`; observation/storage/test helpers live in `rtl/amba/shared/`; CDC helpers moved OUT to the top-level `rtl/cdc/` area (AMBA-CDC-REORG) -- see `rtl/cdc/CLAUDE.md`. The wrappers instantiate the monitor-core pieces below.

**Monitor core (13):**

| Module | Purpose |
|---|---|
| `axi_monitor_base.sv` | Top-level scaffold (every `*_mon` wrapper instantiates this) |
| `axi_monitor_trans_mgr.sv` | Outstanding-transaction table; `active_count` pipelined to close 100 MHz |
| `axi_monitor_addr_check.sv` | Address range / region filtering |
| `axi_monitor_filtered.sv` | Configurable per-channel packet filtering |
| `axi_monitor_timer.sv` | Free-running timer + per-transaction stamps |
| `axi_monitor_timeout.sv` | Timeout detection |
| `axi_monitor_reporter.sv` | Packet generation dispatcher (post-refactor: delegates to subblocks below) |
| `axi_monitor_reporter_{compl,debug,error,perf,threshold,timeout}.sv` | One per packet type (6 files) |
| `monitor_trans_cam.sv` | CAM lookup for trans_mgr |

**Observation / performance (3):**

| Module | Purpose |
|---|---|
| `axi4_dma_observer.sv` | DMA observability wrapper. Per-channel AW→W AWID order tracker (no sideband). Per-port latency histograms for parity with in-core perfmon |
| `axi_perf_latency_hist.sv` | Per-channel 16-bucket log2 latency histogram |
| `axi_bus_meter.sv` | 4-bucket bus meter (productive / backpressure / starvation / idle) — see `DMA_UTILIZATION_MEASUREMENT.md` for window semantics |

**Monitor Bus (monbus) infrastructure (10):**

| Module | Purpose |
|---|---|
| `monbus_arbiter.sv` | Top-level monbus arbitration |
| `monbus_group_core.sv` | Shared filter + FIFO core for all `monbus_*_*_group` wrappers (refactor introduced in `61edda71`) |
| `monbus_axi4_axi4_group.sv` | AXI4↔AXI4 group |
| `monbus_axi4_axil_group.sv` | AXI4↔AXIL group |
| `monbus_axil_axi4_group.sv` | AXIL↔AXI4 group with 32-bit err-drain |
| `monbus_axil_axil_group.sv` | AXIL↔AXIL group with 32-bit err-drain |
| `monbus_compressor.sv` | Optional packet compressor (mod-3 packing). Runtime enable via `cfg_compress_en` |
| `monbus_halfbeat_packer.sv` | Half-beat packer pushing past the compressor's 66.7% ceiling |
| `monbus_cam.sv` / `monbus_cam_pipe.sv` | Monbus CAM for packet matching/replay (and pipelined variant) |

**Arbiters with monbus instrumentation (3):** `arbiter_monbus_common.sv`, `arbiter_rr_pwm_monbus.sv`, `arbiter_wrr_pwm_monbus.sv`

**CDC (moved):** `cdc_2_phase_handshake.sv`, `cdc_4_phase_handshake.sv`, `cdc_open_loop.sv` and `cdc_synchronizer.sv` now live in `rtl/cdc/`, along with `gaxi_fifo_async.sv` and `gaxi_skid_buffer_async.sv` that used to sit under `rtl/amba/gaxi/`. Docs: `docs/markdown/RTLCdc/`.

**Storage helpers (5)** — used by harnesses, not the monitor path itself: `sdpram_core.sv` (shared core) + `sdpram_slave_{axi4,axil}_{axi4,axil}.sv` (4 protocol-pair wrappers). Replaces the deleted unified `sdpram_slave.sv`.

**Test infrastructure helpers:** `axi4_dma_slaves.sv`, `axi4_slave_rd_pattern_gen.sv`, `axi4_slave_wr_crc_check.sv`, `axi_master_{rd,wr}_splitter.sv`, `axi_split_combi.sv`, `axi_gen_addr.sv`, `amba_clock_gate_ctrl.sv`, `apb_monitor_addr_check.sv`

**Removed:** the prior `mon_temp/` legacy `trans_mgr` (deleted in `d246a72d`) and the unified `sdpram_slave.sv` (replaced by `sdpram_core.sv` + 4 wrappers). Don't reference these in new code.

---

## Common User Questions and Responses

### Q: "How do I monitor my AXI4 master?"

**A: Direct answer with code:**
```systemverilog
axi4_master_rd_mon #(
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),
    .MAX_TRANSACTIONS(16)
) u_axi_mon (
    .aclk    (axi_clk),
    .aresetn (axi_rst_n),
    // Connect AXI signals: axi_ar*, axi_r*
    .monbus_valid (mon_valid),
    .monbus_ready (mon_ready),
    .monbus_packet  (mon_data),
    // Configuration
    .cfg_error_enable   (1'b1),
    .cfg_compl_enable   (1'b1),
    .cfg_timeout_enable (1'b1),
    .cfg_perf_enable    (1'b0)  // ⚠️ Disable to avoid congestion
);

// Add downstream FIFO
gaxi_fifo_sync #(.DATA_WIDTH(128), .DEPTH(256)) u_fifo (
    .i_clk(axi_clk), .i_rst_n(axi_rst_n),
    .i_valid(mon_valid), .i_data(mon_data), .o_ready(mon_ready),
    // ... connect to your packet consumer
);
```

**Then link:**
- **Integration:** See `docs/markdown/RTLAmba/index.md` for complete examples
- **Configuration:** See `docs/user-guides/AXI_Monitor_Configuration_Guide.md`
- **Module spec:** See `docs/markdown/RTLAmba/monitor/axi4_master_rd_mon.md`

### Q: "What packet types should I enable?"

**A: Depends on use case:**

**Functional Verification (most common):**
```systemverilog
.cfg_error_enable   (1'b1),  // Catch SLVERR, DECERR, orphans
.cfg_compl_enable   (1'b1),  // Track completions
.cfg_timeout_enable (1'b1),  // Detect stuck transactions
.cfg_perf_enable    (1'b0),  // ⚠️ DISABLE (high traffic)
.cfg_debug_enable   (1'b0)   // Only if deep debugging
```

**Performance Analysis:**
```systemverilog
.cfg_error_enable   (1'b1),  // Still catch errors
.cfg_compl_enable   (1'b0),  // ⚠️ DISABLE (reduce traffic)
.cfg_timeout_enable (1'b0),  // Disable
.cfg_perf_enable    (1'b1),  // Enable performance metrics
.cfg_debug_enable   (1'b0)
```

**⚠️ CRITICAL:** "Never enable completions + performance together!"

**📖 See:** `docs/user-guides/AXI_Monitor_Configuration_Guide.md` (comprehensive guide)

### Q: "Monitor packets format?"

**A: 128-bit standardized `monitor_packet_t` + 64-bit side-band timestamp**
(`monitor_common_pkg.sv`; widths locked, not parameters):
```
[127:124] Packet Type  (0=ERROR, 1=COMPL, 2=THRESH, 3=TIMEOUT, 4=PERF,
                        8=ADDR_MATCH, 9=APB, 0xD=PERFWIN, 0xE=PERFHIST,
                        0xF=DEBUG)
[123:109] Reserved     (15 bits, forward-compat slack)
[108:105] Protocol     (0=AXI, 1=AXIS, 2=APB, 3=ARB, 4=CORE)
[104:97]  Event Code   (8 bits)
[96:88]   Channel ID   (9 bits)
[87:72]   Agent ID     (16 bits)
[71:64]   Unit ID      (8 bits)
[63:0]    Event Data   (full 64-bit address, latency, counts, etc.)
```

**Decode example:**
```systemverilog
logic [3:0]  pkt_type   = monbus_packet[127:124];
logic [3:0]  protocol   = monbus_packet[108:105];
logic [63:0] event_data = monbus_packet[63:0];
// or use monitor_common_pkg::get_packet_type() etc.
```

**📖 See:** `docs/markdown/RTLAmba/includes/monitor_package_spec.md` (complete spec)

### Q: "How to handle multiple monitors?"

**A: Use arbiter to aggregate:**
```systemverilog
// Multiple monitors
wire [N-1:0] mon_valid;
wire [N-1:0][127:0] mon_data;  // 128-bit monitor packets
wire [N-1:0] mon_ready;

// Arbiter aggregates packets
arbiter_rr_monbus #(
    .N(N),
    .DATA_WIDTH(128)
) u_mon_arbiter (
    .i_clk     (clk),
    .i_rst_n   (rst_n),
    .i_request (mon_valid),
    .i_data    (mon_data),
    .o_grant   (mon_ready),
    .o_valid   (agg_valid),
    .o_data    (agg_data)
);

// Downstream FIFO for aggregated stream
gaxi_fifo_sync #(.DATA_WIDTH(128), .DEPTH(1024)) u_agg_fifo (
    .i_valid (agg_valid),
    .i_data  (agg_data),
    // ... to system consumer
);
```

### Q: "What's MAX_TRANSACTIONS?"

**A: Transaction table size:**
- Tracks up to MAX_TRANSACTIONS concurrent transactions
- Must be >= maximum outstanding transactions on bus
- **Shared master:** must cover NUM_CHANNELS x per-channel outstanding
  (+ margin) — sizing to the per-channel limit alone throttles the shared
  bus (this exact mistake shipped in stream_core; fixed in `95c9490a`)
- **Typical values:**
  - AXI4: 16-32 (supports burst, out-of-order)
  - AXI4-Lite: 4-8 (single-beat only)
  - APB: 2-4 (simple protocol)

**If too small (saturation-recovery contract, `cb29e226`):**
- New commands are throttled at the upstream handshake via the internal
  `block_ready` gate (transaction-TABLE occupancy, not the reporter FIFO)
- Tables of 16+ reserve `cmd_entry_reserve(MAX)=2` slots so `block_ready`
  always recovers — blocking throttles, never deadlocks; tables <16 keep
  full legacy allocation and trade the recovery guarantee for capacity
- Commands seen while capped are simply not tracked (lossy-but-honest)

**Verilator note:** tables deeper than 64 need `--unroll-count` raised
(default 64) in sim builds or the per-slot loops fail BLKLOOPINIT.

**Recommendation:** "Use 16-32 for AXI4, can reduce for simpler protocols"

### Q: "Why are tests failing?"

**A: Check current status first:**

```bash
# View test results
pytest val/amba/test_axi4_monitor.py -v
```

**Current Known Issues:**
- ✅ **Event reported bug:** FIXED (2025-09-30)
- ✅ **Saturation wedge / runtime-disable leak:** FIXED (`cb29e226`, `95c9490a`)
- val/amba is fully green; if a monitor test fails, suspect the change under test or the framework, not a documented known issue

**If user reports test failure:**
1. Check `rtl/amba/KNOWN_ISSUES/` for documented issues
2. Run test with `-v -s` for verbose output
3. Check if it's a known test configuration issue

**📖 See:** `rtl/amba/KNOWN_ISSUES/README.md`

---

## Integration Patterns

### Pattern 1: Basic AXI Monitor

```systemverilog
axi4_master_rd_mon #(
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),
    .MAX_TRANSACTIONS(16)
) u_mon (
    .aclk(clk), .aresetn(rst_n),
    // AXI AR channel
    .axi_arid(m_axi_arid), .axi_araddr(m_axi_araddr),
    .axi_arlen(m_axi_arlen), .axi_arsize(m_axi_arsize),
    .axi_arburst(m_axi_arburst),
    .axi_arvalid(m_axi_arvalid), .axi_arready(m_axi_arready),
    // AXI R channel
    .axi_rid(m_axi_rid), .axi_rdata(m_axi_rdata),
    .axi_rresp(m_axi_rresp), .axi_rlast(m_axi_rlast),
    .axi_rvalid(m_axi_rvalid), .axi_rready(m_axi_rready),
    // Monitor bus
    .monbus_valid(mon_valid),
    .monbus_ready(mon_ready),
    .monbus_packet(mon_data),
    // Config
    .cfg_error_enable(1'b1), .cfg_compl_enable(1'b1),
    .cfg_timeout_enable(1'b1), .cfg_perf_enable(1'b0)
);
```

### Pattern 2: APB Monitor

```systemverilog
apb_monitor #(
    .ADDR_WIDTH(16),
    .DATA_WIDTH(32),
    .MAX_TRANSACTIONS(8)
) u_apb_mon (
    .pclk(apb_clk), .presetn(apb_rst_n),
    .paddr(apb_paddr), .psel(apb_psel),
    .penable(apb_penable), .pwrite(apb_pwrite),
    .pwdata(apb_pwdata), .pready(apb_pready),
    .prdata(apb_prdata), .pslverr(apb_pslverr),
    .monbus_valid(mon_valid),
    .monbus_ready(mon_ready),
    .monbus_packet(mon_data),
    .cfg_error_enable(1'b1), .cfg_compl_enable(1'b1)
);
```

### Pattern 3: AXIS Monitor

```systemverilog
axis_master #(
    .DATA_WIDTH(64),
    .ID_WIDTH(8),
    .DEST_WIDTH(4)
) u_axis_mon (
    .aclk(clk), .aresetn(rst_n),
    .m_axis_tdata(axis_tdata),
    .m_axis_tkeep(axis_tkeep),
    .m_axis_tlast(axis_tlast),
    .m_axis_tvalid(axis_tvalid),
    .m_axis_tready(axis_tready),
    .monbus_valid(mon_valid),
    .monbus_packet(mon_data)
);
```

### Pattern 4: Monitor with Downstream FIFO

```systemverilog
// Always add FIFO for robustness
gaxi_fifo_sync #(
    .DATA_WIDTH(64),
    .DEPTH(256)
) u_mon_fifo (
    .i_clk(clk), .i_rst_n(rst_n),
    .i_data(monbus_pkt_data),
    .i_valid(monbus_pkt_valid),
    .o_ready(monbus_pkt_ready),
    .o_data(fifo_data),
    .o_valid(fifo_valid),
    .i_ready(consumer_ready)
);
```

### Pattern 5: Clock-Gated Monitor (Power)

```systemverilog
axi4_master_rd_mon_cg #(
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64)
) u_mon_cg (
    .aclk(axi_clk), .aresetn(axi_rst_n),
    .cg_enable(monitor_active),  // Clock gate control
    // ... rest of connections same as non-CG variant
);
```

---

## Anti-Patterns to Catch

### ❌ Anti-Pattern 1: Packet Congestion

```systemverilog
❌ WRONG:
.cfg_error_enable(1'b1),
.cfg_compl_enable(1'b1),
.cfg_perf_enable(1'b1),      // TOO MUCH!
.cfg_debug_enable(1'b1)      // WAY TOO MUCH!

✅ CORRECTED:
"Never enable all packet types! Use separate test configurations:
- Functional debug: error + compl + timeout
- Performance: error + perf (disable compl!)
See docs/user-guides/AXI_Monitor_Configuration_Guide.md"
```

### ❌ Anti-Pattern 2: No Downstream Handling

```systemverilog
❌ WRONG:
assign monbus_ready = 1'b1;  // Always ready

✅ CORRECTED:
"Connect to FIFO or proper consumer:
gaxi_fifo_sync #(.DATA_WIDTH(128), .DEPTH(256)) u_fifo (
    .i_valid(monbus_valid),
    .i_data(monbus_packet),
    .o_ready(monbus_ready),
    ...
);
"
```

### ❌ Anti-Pattern 3: Wrong MAX_TRANSACTIONS

```systemverilog
❌ WRONG:
.MAX_TRANSACTIONS(2)  // Too small for burst traffic

✅ CORRECTED:
"For AXI4 with bursts, use MAX_TRANSACTIONS >= 16.
Current value (2) is too small for realistic traffic."
```

### ❌ Anti-Pattern 4: Missing Configuration

```systemverilog
❌ WRONG:
axi4_master_rd_mon u_mon (
    // ... signals ...
    // ❌ No cfg_*_enable signals!
);

✅ CORRECTED:
"Must set configuration signals:
.cfg_error_enable(1'b1),
.cfg_compl_enable(1'b1),
.cfg_timeout_enable(1'b1),
.cfg_perf_enable(1'b0)
"
```

---

## Debugging Workflow

### Issue: No Monitor Packets

**Check in order:**
1. ✅ Configuration enables correct packet types?
2. ✅ Monitor bus ready signal asserted?
3. ✅ AXI/APB transactions actually occurring?
4. ✅ Reset properly deasserted?
5. ✅ Downstream path not stalled?

**Debug commands:**
```bash
pytest val/amba/test_axi4_monitor.py -v -s  # Verbose test
pytest val/amba/test_axi4_monitor.py --vcd=debug.vcd
gtkwave debug.vcd
```

### Issue: Test Failures

**Check known issues:**
```bash
ls rtl/amba/KNOWN_ISSUES/
cat rtl/amba/KNOWN_ISSUES/README.md
```

**Current status:**
- ✅ Event reported bug FIXED
- ⚠️ 2 test config issues (non-RTL)

### Issue: Transaction Table Exhaustion

**Symptoms:**
- Monitor stops generating packets
- Logs show "MAX_TRANSACTIONS reached"

**Fixes:**
1. Increase MAX_TRANSACTIONS
2. Verify transactions completing (RLAST/BVALID)
3. Check for protocol violations

**Note:** "Recent fix (2025-09-30) added event_reported feedback - should no longer occur"

---

## Testing Guidance

### Run Tests

```bash
# Single test
pytest val/amba/test_axi4_monitor.py -v

# All AMBA tests
pytest val/amba/ -v

# Specific protocol
pytest val/amba/test_apb_monitor.py -v

# With waveforms
pytest val/amba/test_axi4_monitor.py --vcd=waves.vcd
gtkwave waves.vcd
```

### Test Status (Current)

**AXI Monitor (as of `95c9490a`):** val/amba fully green — 679 passed / 0 failed
- ✅ Basic / Burst / Outstanding / ID reorder / Backpressure / Timeout
- ✅ Error response / Orphan
- ✅ Saturation recovery (`test_axi_monitor_trans_mgr.py`)
- ✅ Runtime-disable auto-retire (`test_axi_monitor_runtime_disable.py`)
- ✅ Same-cycle AW+W (`test_axi_monitor_wr_same_cycle.py`)
- ✅ Wrapper cfg API (`test_axi4_master_rd_mon_cfg.py`)

---

## Key Documentation Links

### Always Reference These

**Primary Technical Docs:**
- `docs/markdown/RTLAmba/index.md` - Module index
- `docs/markdown/RTLAmba/overview.md` - Architecture
- `docs/markdown/RTLAmba/axi4/` + `docs/markdown/RTLAmba/monitor/` - AXI module and monitor specs
- `docs/markdown/RTLAmba/apb/` - APB module specs
- `docs/markdown/RTLAmba/axis4/` - AXIS module specs
- `docs/markdown/RTLAmba/includes/monitor_package_spec.md` - Packet format

**Configuration:**
- `docs/user-guides/AXI_Monitor_Configuration_Guide.md` ← **Essential for correct setup**

**This Subsystem:**
- `docs/markdown/RTLAmba/index.md` - Requirements overview
- `docs/markdown/RTLAmba/index.md` - Quick start guide
- `/vault/Tasks/amba/` - Current work
- `rtl/amba/KNOWN_ISSUES/` - Bug tracking

**Root:**
- `/PRD.md` - Master requirements
- `/CLAUDE.md` - Repository guide

---

## Quick Commands

```bash
# View detailed docs
cat docs/markdown/RTLAmba/overview.md
cat docs/markdown/RTLAmba/monitor/axi4_master_rd_mon.md

# Check configuration guide
cat docs/user-guides/AXI_Monitor_Configuration_Guide.md

# Run tests
pytest val/amba/test_axi4_monitor.py -v

# Check known issues
ls rtl/amba/KNOWN_ISSUES/
cat rtl/amba/KNOWN_ISSUES/README.md

# Lint
verilator --lint-only rtl/amba/monitor/axi_monitor_base.sv
```

---

## Remember

1. 📖 **Link to detailed docs** - `docs/markdown/RTLAmba/` has complete specs
2. ⚠️ **Configuration critical** - Never all packet types together
3. 🐛 **Check known issues** - Before diagnosing bugs
4. 🔗 **Complete integration** - Monitor + config + downstream handling
5. ✅ **Test awareness** - val/amba fully green as of `95c9490a`; open items are non-monitor (STREAM 8ch engine wedge) or framework (axil4 TB drain race)

---

**Version:** 1.0
**Last Updated:** 2025-09-30
**Maintained By:** RTL Design Sherpa Project
