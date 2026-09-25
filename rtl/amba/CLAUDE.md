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
**Status:** Active development - production-ready monitors, test refinement ongoing
**Your Role:** Help users integrate monitors, configure correctly, debug issues

**Detailed Specs:** `docs/markdown/rtl-amba/` ← **Always reference this for technical details**

---

## Global Requirements Reference

**IMPORTANT: Check `/GLOBAL_REQUIREMENTS.md` for mandatory verification standards**

All mandatory requirements are consolidated in the global requirements document:
- **See:** `/GLOBAL_REQUIREMENTS.md` - Repository-wide mandatory requirements
- **AMBA Focus:** Three-layer architecture, queue-based verification, 100% success
- **Universal:** TB location, TBBase inheritance, test naming conventions

This CLAUDE.md provides AMBA-specific guidance. Also review:
- Root `/CLAUDE.md` - Repository-wide patterns
- RDS-DV framework docs: `../RTLDesignSherpa-DV/docs/components/<family>/`
  (published at sean-galloway.github.io/RTLDesignSherpa-DV) - per-protocol BFM
  and monitor usage. `docs/markdown/TBClasses/` does not exist.
- `docs/user-guides/VERIFICATION_ARCHITECTURE_GUIDE.md` - Complete verification patterns

---

## Critical Rules for This Subsystem

### Rule #0: Where the verification code lives

TB classes are in `bin/TBClasses/<protocol>/` (`axi4/`, `axi_monitor/`,
`apb4_monitor/`, ...); the runners that import them are `val/amba/test_*.py`.
How a TB is composed -- the three-layer split, and when to score with a queue
versus a memory model -- is repo-wide practice, not an AMBA rule:
`vault/handbook/dv/tb-structure.md`. `/GLOBAL_REQUIREMENTS.md` 2.1/2.3/2.4 is
the enforcement authority and wins on conflict.

Module specs are under `docs/markdown/rtl-amba/`; link to the specific page
rather than restating a port list here.

---

### Rule #1: Avoid Enabling All Monitor Packet Types

**This is the #1 integration mistake!** The monitor bus sustains at most
1 packet per 2 cycles (reporter output register), so enabling every
packet class under heavy traffic congests it.

```systemverilog
WRONG (User's code):
.cfg_error_enable   (1'b1),
.cfg_compl_enable   (1'b1),
.cfg_perf_enable    (1'b1),  // PACKET CONGESTION!
.cfg_debug_enable   (1'b1)   // EVEN WORSE!

CORRECT (Functional debug mode):
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

### Rule #2: Know the Known Issues

**Current Status (as of `95c9490a`):**
- Event reported feedback bug FIXED (2025-09-30)
- Multi-channel saturation wedge FIXED (`cb29e226`)
- Runtime-disable leak / same-cycle AW+W / wrapper API / AXI5 W wiring FIXED (`95c9490a`)
- val/amba regression fully green (679 passed / 0 failed); monitor formal 10/10
- Open (framework): axil4 monitor TB drain-window race — seeds pinned; proper fix in RDS-DV

**Always check:** `rtl/amba/KNOWN_ISSUES/` before diagnosing bugs

```bash
ls rtl/amba/KNOWN_ISSUES/   # 3 pages: active_count underflow,
                            # block_ready hang, orphan error flood
```

### Rule #3: Integration = Configuration + Wiring + Downstream

**Complete integration requires:**
1. Module instantiation with correct parameters
2. Configuration signals (cfg_*_enable)
3. **Downstream monitor bus handling** (FIFO, arbiter, or consumer)

**Incomplete example:**
```systemverilog
INCOMPLETE:
axi4_master_rd_mon u_mon (
    // ... AXI signals ...
    .monbus_valid (mon_valid),
    .monbus_packet  (mon_data),
    .monbus_ready (1'b1)  // Always ready = packet loss risk!
);
```

**Complete example:**
```systemverilog
COMPLETE:
// Monitor
axi4_master_rd_mon u_mon (
    // ... AXI signals ...
    .monbus_valid (mon_valid),
    .monbus_packet  (mon_data),
    .monbus_ready (fifo_ready)
);

// Downstream FIFO
gaxi_fifo_sync #(.REGISTERED(0), .DATA_WIDTH(128), .DEPTH(256)) u_fifo (
    .axi_aclk    (aclk),
    .axi_aresetn (aresetn),
    .wr_valid    (mon_valid),
    .wr_data     (mon_data),
    .wr_ready    (fifo_ready),   // "not full" -- drive monbus_ready with this
    .rd_valid    (consumer_valid),
    .rd_ready    (consumer_ready),
    .rd_data     (consumer_data),
    /* verilator lint_off PINCONNECTEMPTY */
    .count       ()
    /* verilator lint_on PINCONNECTEMPTY */
);
```

---

## Module Quick Reference

### AXI4 Monitors

| Module | Purpose | Key Params | Documentation |
|--------|---------|------------|---------------|
| `axi4_master_rd_mon.sv` | Master read monitoring (inline: `fub_axi_*` in, `m_axi_*` out) | AXI_ID_WIDTH, AXI_ADDR_WIDTH, AXI_DATA_WIDTH, MAX_TRANSACTIONS | `docs/markdown/rtl-amba/axi4/axi4_master_rd_mon.md` |
| `axi4_master_wr_mon.sv` | Master write monitoring | Same | `docs/markdown/rtl-amba/axi4/axi4_master_wr_mon.md` |
| `axi4_slave_rd_mon.sv` | Slave read monitoring | Same | `docs/markdown/rtl-amba/axi4/axi4_slave_rd_mon.md` |
| `axi4_slave_wr_mon.sv` | Slave write monitoring | Same | `docs/markdown/rtl-amba/axi4/axi4_slave_wr_mon.md` |
| `*_cg.sv` variants | Clock-gated versions | Same + CG_IDLE_COUNT_WIDTH (ports: `cfg_cg_enable`, `cfg_cg_idle_count`, `cg_gating`, `cg_idle`) | Power optimization |

### APB Monitors

| Module | Purpose | Key Params | Documentation |
|--------|---------|------------|---------------|
| `apb4_monitor.sv` | APB transaction monitoring | ADDR_WIDTH, DATA_WIDTH, MAX_TRANSACTIONS | `docs/markdown/rtl-amba/apb4/` |

### AXIS Monitors

| Module | Purpose | Key Params | Documentation |
|--------|---------|------------|---------------|
| `axis_bus_meter.sv` | Stream throughput / backpressure counters. **The only AXIS-side measurement block** | DATA_WIDTH, NUM_CHANNELS | `docs/markdown/rtl-amba/shared/axis_bus_meter.md` |

> **There is no AXIS monbus monitor.** `axis4_master.sv` and `axis4_slave.sv`
> are skid-buffered stream endpoints (`AXIS_DATA_WIDTH`, `AXIS_ID_WIDTH`,
> `AXIS_DEST_WIDTH`) and carry zero monbus ports; this table called them
> "AXIS transmit/receive monitoring" for months. Measured: no module under
> `rtl/amba/axis4/` declares a monbus port.

### AXI4-Lite Monitors

| Module | Purpose | Key Params | Documentation |
|--------|---------|------------|---------------|
| `axil4_master_rd_mon.sv` | AXIL master read monitoring | AXIL_ADDR_WIDTH, AXIL_DATA_WIDTH, MAX_TRANSACTIONS | `rtl/amba/axil4/` |
| `axil4_master_wr_mon.sv` | AXIL master write monitoring | Same | `rtl/amba/axil4/` |
| `axil4_slave_rd_mon.sv` | AXIL slave read monitoring | Same | `rtl/amba/axil4/` |
| `axil4_slave_wr_mon.sv` | AXIL slave write monitoring | Same | `rtl/amba/axil4/` |
| `*_cg.sv` variants | Clock-gated AXIL versions | Same + CG_IDLE_COUNT_WIDTH (ports: `cfg_cg_enable`, `cfg_cg_idle_count`, `cg_gating`, `cg_idle`) | Power optimization |

> Dedicated AXIL4 wrappers (not the old `IS_AXI=0` parameter overload). Share `axi_monitor_base` and packet format with the AXI4 wrappers.

### Supporting Infrastructure — `rtl/amba/monitor/` + `rtl/amba/shared/`

All protocol-agnostic. The monitor core, monbus infrastructure and monbus arbiters live in `rtl/amba/monitor/`. The protocol `*_mon` wrappers do NOT -- each lives with the protocol it wraps (`axi4/`, `axi5/`, `axil4/`, `apb/`, `apb5/`), because a wrapper pairs one protocol block with the shared core and belongs to the protocol, not to the core; observation/storage/test helpers live in `rtl/amba/shared/`; CDC helpers moved OUT to the top-level `rtl/cdc/` area (AMBA-CDC-REORG) -- see `rtl/cdc/CLAUDE.md`. The wrappers instantiate the monitor-core pieces below.

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
| `axi_perf_latency_hist.sv` | Per-channel 16-bucket log2 latency histogram |
| `axi_bus_meter.sv` | 4-bucket bus meter (productive / backpressure / starvation / idle) — see `DMA_UTILIZATION_MEASUREMENT.md` for window semantics |

**Monitor Bus (monbus) infrastructure (10):**

| Module | Purpose |
|---|---|
| `monbus_arbiter.sv` | Top-level monbus arbitration |
| `monbus_group_core.sv` | Shared filter + FIFO core for all `monbus_*_*_group` wrappers (refactor introduced in `61edda71`) |
| `monbus_axi4_axi4_group.sv` | AXI4↔AXI4 group |
| `monbus_axi4_axil4_group.sv` | AXI4↔AXIL group |
| `monbus_axil4_axi4_group.sv` | AXIL↔AXI4 group with 32-bit err-drain |
| `monbus_axil4_axil4_group.sv` | AXIL↔AXIL group with 32-bit err-drain |
| `monbus_compressor.sv` | Optional packet compressor (mod-3 packing). Runtime enable via `cfg_compress_en` |
| `monbus_halfbeat_packer.sv` | Half-beat packer pushing past the compressor's 66.7% ceiling |
| `monbus_cam.sv` / `monbus_cam_pipe.sv` | Monbus CAM for packet matching/replay (and pipelined variant) |

**Arbiters with monbus instrumentation (3):** `arbiter_monbus_common.sv`, `arbiter_rr_pwm_monbus.sv`, `arbiter_wrr_pwm_monbus.sv`

**CDC (moved):** `cdc_2_phase_handshake.sv`, `cdc_4_phase_handshake.sv`, `cdc_open_loop.sv` and `cdc_synchronizer.sv` now live in `rtl/cdc/`, along with `gaxi_fifo_async.sv` and `gaxi_skid_buffer_async.sv` that used to sit under `rtl/amba/gaxi/`. Docs: `docs/markdown/rtl-cdc/`.

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
    .cfg_perf_enable    (1'b0)  // Disable to avoid congestion
);

// Add downstream FIFO
gaxi_fifo_sync #(.REGISTERED(0), .DATA_WIDTH(128), .DEPTH(256)) u_fifo (
    .axi_aclk    (aclk),
    .axi_aresetn (aresetn),
    .wr_valid    (mon_valid),
    .wr_data     (mon_data),
    .wr_ready    (fifo_ready),   // "not full" -- drive monbus_ready with this
    .rd_valid    (consumer_valid),
    .rd_ready    (consumer_ready),
    .rd_data     (consumer_data),
    /* verilator lint_off PINCONNECTEMPTY */
    .count       ()
    /* verilator lint_on PINCONNECTEMPTY */
);
```

**Then link:**
- **Integration:** See `docs/markdown/rtl-amba/index.md` for complete examples
- **Configuration:** See `docs/user-guides/AXI_Monitor_Configuration_Guide.md`
- **Module spec:** See `docs/markdown/rtl-amba/axi4/axi4_master_rd_mon.md`

### Q: "What packet types should I enable?"

**A: Depends on use case:**

**Functional Verification (most common):**
```systemverilog
.cfg_error_enable   (1'b1),  // Catch SLVERR, DECERR, orphans
.cfg_compl_enable   (1'b1),  // Track completions
.cfg_timeout_enable (1'b1),  // Detect stuck transactions
.cfg_perf_enable    (1'b0),  // DISABLE (high traffic)
.cfg_debug_enable   (1'b0)   // Only if deep debugging
```

**Performance Analysis:**
```systemverilog
.cfg_error_enable   (1'b1),  // Still catch errors
.cfg_compl_enable   (1'b0),  // DISABLE (reduce traffic)
.cfg_timeout_enable (1'b0),  // Disable
.cfg_perf_enable    (1'b1),  // Enable performance metrics
.cfg_debug_enable   (1'b0)
```

**CRITICAL:** "Never enable completions + performance together!"

**See:** `docs/user-guides/AXI_Monitor_Configuration_Guide.md` (comprehensive guide)

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

**See:** `docs/markdown/rtl-amba/includes/monitor_package_spec.md` (complete spec)

### Q: "How to handle multiple monitors?"

**A: Use arbiter to aggregate:**
```systemverilog
// Multiple monitors. monbus_arbiter takes UNPACKED arrays, one entry per
// client, and the packet is monitor_packet_t -- not a bare [127:0] bus.
logic              mon_valid     [CLIENTS];
logic              mon_ready     [CLIENTS];
monitor_packet_t   mon_packet    [CLIENTS];
monbus_timestamp_t mon_timestamp [CLIENTS];

monbus_arbiter #(
    .CLIENTS (CLIENTS)
) u_mon_arbiter (
    .axi_aclk            (aclk),
    .axi_aresetn         (aresetn),
    .block_arb           (1'b0),
    .monbus_valid_in     (mon_valid),
    .monbus_ready_in     (mon_ready),
    .monbus_packet_in    (mon_packet),
    .monbus_timestamp_in (mon_timestamp),
    .monbus_valid        (agg_valid),
    .monbus_ready        (agg_ready),
    .monbus_packet       (agg_packet),
    .monbus_timestamp    (agg_timestamp),
    .grant_valid         (),
    .grant               (),
    .grant_id            ()
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
- Tables of 16+ reserve `cmd_entry_reserve(MAX)=4` slots so `block_ready`
  always recovers — blocking throttles, never deadlocks; tables <16 keep
  full legacy allocation and trade the recovery guarantee for capacity
- Commands seen while capped are simply not tracked (lossy-but-honest)

**Verilator note:** tables deeper than 64 need `--unroll-count` raised
(default 64) in sim builds or the per-slot loops fail BLKLOOPINIT.

**Recommendation:** "Use 16-32 for AXI4, can reduce for simpler protocols"

### Q: "Why are tests failing?"

**A: Check current status first:**

```bash
# Through the area Makefile (see vault/handbook/dv/running-regressions.md)
cd val/amba && make run-axi4_monitor-gate
```

**Current Known Issues:**
- **Event reported bug:** FIXED (2025-09-30)
- **Saturation wedge / runtime-disable leak:** FIXED (`cb29e226`, `95c9490a`)
- val/amba is fully green; if a monitor test fails, suspect the change under test or the framework, not a documented known issue

**If user reports test failure:**
1. Check `rtl/amba/KNOWN_ISSUES/` for documented issues
2. Run test with `-v -s` for verbose output
3. Check if it's a known test configuration issue

**See:** `rtl/amba/KNOWN_ISSUES/` -- three issue pages, no index README

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
    // This module sits INLINE: fub_* is the upstream (FUB) side, m_axi_* the
    // downstream side. It is not a passive snooper on one bus.
    .fub_axi_arid(fub_arid), .fub_axi_araddr(fub_araddr),
    .fub_axi_arlen(fub_arlen), .fub_axi_arsize(fub_arsize),
    .fub_axi_arburst(fub_arburst),
    .fub_axi_arvalid(fub_arvalid), .fub_axi_arready(fub_arready),
    .fub_axi_rid(fub_rid), .fub_axi_rdata(fub_rdata),
    .fub_axi_rresp(fub_rresp), .fub_axi_rlast(fub_rlast),
    .fub_axi_rvalid(fub_rvalid), .fub_axi_rready(fub_rready),
    .m_axi_arid(m_axi_arid), .m_axi_araddr(m_axi_araddr),
    .m_axi_arlen(m_axi_arlen), .m_axi_arsize(m_axi_arsize),
    .m_axi_arburst(m_axi_arburst),
    .m_axi_arvalid(m_axi_arvalid), .m_axi_arready(m_axi_arready),
    .m_axi_rid(m_axi_rid), .m_axi_rdata(m_axi_rdata),
    .m_axi_rresp(m_axi_rresp), .m_axi_rlast(m_axi_rlast),
    .m_axi_rvalid(m_axi_rvalid), .m_axi_rready(m_axi_rready),
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
apb4_monitor #(
    .ADDR_WIDTH(16),
    .DATA_WIDTH(32),
    .MAX_TRANSACTIONS(8)
) u_apb_mon (
    // NOT raw APB pins: this monitor watches the converted cmd/rsp interface
    // in the aclk domain, which is what apb4_slave/apb4_master_stub present.
    .aclk(aclk), .aresetn(aresetn),
    .cmd_valid(cmd_valid), .cmd_ready(cmd_ready),
    .cmd_pwrite(cmd_pwrite), .cmd_paddr(cmd_paddr),
    .cmd_pwdata(cmd_pwdata), .cmd_pstrb(cmd_pstrb), .cmd_pprot(cmd_pprot),
    .rsp_valid(rsp_valid), .rsp_ready(rsp_ready),
    .rsp_prdata(rsp_prdata), .rsp_pslverr(rsp_pslverr),
    .monbus_valid(mon_valid),
    .monbus_ready(mon_ready),
    .monbus_packet(mon_data),
    // apb4_monitor has no completion concept; these are its real cfg ports
    .cfg_error_enable(1'b1), .cfg_slverr_enable(1'b1),
    .cfg_protocol_enable(1'b1), .cfg_timeout_enable(1'b1)
);
```

### Pattern 3: AXIS measurement (there is NO AXIS monbus monitor)

No module on the stream side emits monbus -- `axis4_master`/`axis4_slave` are
skid-buffered stream endpoints, not monitors. For throughput and backpressure
on a stream, snoop it with `axis_bus_meter` and read its counters:

```systemverilog
axis_bus_meter #(
    .DATA_WIDTH   (64),
    .NUM_CHANNELS (8)
) u_axis_meter (
    .aclk(aclk), .aresetn(aresetn),
    .i_clear(meter_clear), .i_freeze(meter_freeze),
    // snoop only -- the meter never drives the bus
    .i_tvalid(axis_tvalid), .i_tready(axis_tready),
    .i_tlast(axis_tlast),   .i_tstrb(axis_tstrb),
    .i_tid(axis_tid),
    .o_agg_productive(prod), .o_agg_backpressure(bp),
    .o_agg_starvation(starv), .o_agg_idle(idle),
    .o_agg_bytes(bytes), .o_agg_beats(beats), .o_agg_packets(packets),
    .o_ch_productive(), .o_ch_backpressure(),
    .o_ch_starvation(), .o_ch_idle(), .o_ch_overflow()
);
```

Worked instance: `rapids_char_harness.sv`. Test: `val/amba/test_axis_bus_meter.py`.

### Pattern 4: Monitor with Downstream FIFO

```systemverilog
// Always add FIFO for robustness
gaxi_fifo_sync #(
    .REGISTERED(0),          // mux read; flop mode re-emits the popped entry
    .DATA_WIDTH(64),
    .DEPTH(256)
) u_mon_fifo (
    .axi_aclk    (aclk),
    .axi_aresetn (aresetn),
    .wr_valid    (monbus_pkt_valid),
    .wr_data     (monbus_pkt_data),
    .wr_ready    (monbus_pkt_ready),
    .rd_valid    (fifo_valid),
    .rd_ready    (consumer_ready),
    .rd_data     (fifo_data),
    /* verilator lint_off PINCONNECTEMPTY */
    .count       ()
    /* verilator lint_on PINCONNECTEMPTY */
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
    .cfg_cg_enable(monitor_active),      // Clock gate control
    .cfg_cg_idle_count(CG_IDLE),         // Idle cycles before gating
    .cg_gating(cg_gating), .cg_idle(cg_idle),
    // ... rest of connections same as non-CG variant
);
```

---

## Anti-Patterns to Catch

### Anti-Pattern 1: Packet Congestion

```systemverilog
WRONG:
.cfg_error_enable(1'b1),
.cfg_compl_enable(1'b1),
.cfg_perf_enable(1'b1),      // TOO MUCH!
.cfg_debug_enable(1'b1)      // WAY TOO MUCH!

CORRECTED:
"Never enable all packet types! Use separate test configurations:
- Functional debug: error + compl + timeout
- Performance: error + perf (disable compl!)
See docs/user-guides/AXI_Monitor_Configuration_Guide.md"
```

### Anti-Pattern 2: No Downstream Handling

```systemverilog
WRONG:
assign monbus_ready = 1'b1;  // Always ready

CORRECTED:
"Connect to FIFO or proper consumer:
gaxi_fifo_sync #(.REGISTERED(0), .DATA_WIDTH(128), .DEPTH(256)) u_fifo (
    .axi_aclk(aclk), .axi_aresetn(aresetn),
    .wr_valid(monbus_valid), .wr_data(monbus_packet),
    .wr_ready(monbus_ready),
    .rd_valid(...), .rd_ready(...), .rd_data(...), .count()
);
"
```

### Anti-Pattern 3: Wrong MAX_TRANSACTIONS

```systemverilog
WRONG:
.MAX_TRANSACTIONS(2)  // Too small for burst traffic

CORRECTED:
"For AXI4 with bursts, use MAX_TRANSACTIONS >= 16.
Current value (2) is too small for realistic traffic."
```

### Anti-Pattern 4: Missing Configuration

```systemverilog
WRONG:
axi4_master_rd_mon u_mon (
    // ... signals ...
    // No cfg_*_enable signals!
);

CORRECTED:
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
1. Configuration enables correct packet types?
2. Monitor bus ready signal asserted?
3. AXI/APB transactions actually occurring?
4. Reset properly deasserted?
5. Downstream path not stalled?

**Debug commands:**
```bash
cd val/amba
make run-axi4_monitor-gate           # verbose by default (-v --tb=short)
make run-axi4_monitor-gate-waves     # WAVES=1; --vcd is not the mechanism
# create_view_cmd() writes a ready-made gtkwave command beside the log
```

### Issue: Test Failures

**Check known issues:**
```bash
ls rtl/amba/KNOWN_ISSUES/   # 3 pages: active_count underflow,
                            # block_ready hang, orphan error flood
```

**Current status:**
- Event reported bug FIXED
- 2 test config issues (non-RTL)

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

`val/amba/Makefile` is four lines over `make/tests.mk`; targets are
`run-<all|testroot>-<gate|func|full>[-serial|-parallel][-waves]`, bare is
parallel, and `clean-all` first is not optional. Full grammar and the reasons:
`vault/handbook/dv/running-regressions.md`.

### Test Status (Current)

**AXI Monitor (as of `95c9490a`):** val/amba fully green — 679 passed / 0 failed
- Basic / Burst / Outstanding / ID reorder / Backpressure / Timeout
- Error response / Orphan
- Saturation recovery (`test_axi_monitor_trans_mgr.py`)
- Runtime-disable auto-retire (`test_axi_monitor_runtime_disable.py`)
- Same-cycle AW+W (`test_axi_monitor_wr_same_cycle.py`)
- Wrapper cfg API (`test_axi4_master_rd_mon_cfg.py`)

---

## Key Documentation Links

### Always Reference These

- `docs/markdown/rtl-amba/` -- module specs, one page per module
  (`index.md`, `overview.md`, then `axi4/`, `apb4/`, `axis4/`, `monitor/`)
- `docs/markdown/rtl-amba/includes/monitor_package_spec.md` -- packet format
- `docs/user-guides/AXI_Monitor_Configuration_Guide.md` -- **read before
  configuring a monitor**; the packet-class rule above is why
- `rtl/amba/KNOWN_ISSUES/` -- open bugs, check before diagnosing
- `/vault/Tasks/amba/` -- current work
- `/GLOBAL_REQUIREMENTS.md` -- enforcement authority
