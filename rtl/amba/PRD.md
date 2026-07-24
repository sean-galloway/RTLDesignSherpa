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

# Product Requirements Document (PRD)
## AMBA Subsystem

**Version:** 1.0
**Date:** 2025-09-30
**Status:** Active Development
**Owner:** RTL Design Sherpa Project
**Parent Document:** `/PRD.md`

---

## 1. Executive Summary

The AMBA subsystem provides comprehensive protocol infrastructure for AXI4, AXI4-Lite, APB, and AXI-Stream interfaces, including transaction monitoring, error detection, and performance analysis capabilities.

### 1.1 Quick Stats

- **Modules:** 72 SystemVerilog files
- **Protocols:** AXI4, AXI4-Lite, APB, AXI-Stream
- **Test Coverage:** ~95% functional
- **Status:** Active development, production-ready monitors
- **Known Issues:** see Section 7.2 (two open items: STREAM 8ch engine wedge, non-monitor; axil4 TB drain race, framework)

### 1.2 Subsystem Goals

- **Primary:** Production-ready AMBA protocol monitors for SoC integration
- **Secondary:** Real-time error detection and performance analysis
- **Tertiary:** Reusable verification infrastructure for AMBA protocols

---

## 2. Documentation Structure

This PRD provides a high-level overview. **Detailed specifications are maintained separately:**

### 📚 Detailed RTL Documentation
**Location:** `docs/markdown/RTLAmba/`

- **[Overview](../../docs/markdown/RTLAmba/overview.md)** - AMBA subsystem architecture
- **[Index](../../docs/markdown/RTLAmba/index.md)** - Complete module listing
- **AXI4 Modules:** `docs/markdown/RTLAmba/axi4/` (monitor wrappers in `docs/markdown/RTLAmba/monitor/`)
  - [AXI4 Master Read](../../docs/markdown/RTLAmba/axi4/axi4_master_rd.md)
  - Additional AXI4 module docs
- **APB Modules:** `docs/markdown/RTLAmba/apb/`
- **AXIS Modules:** `docs/markdown/RTLAmba/axis4/` and `axis5/`
  - [AXIS Master](../../docs/markdown/RTLAmba/axis4/axis_master.md)
- **Monitor Package:** `docs/markdown/RTLAmba/includes/`
  - [Monitor Package Spec](../../docs/markdown/RTLAmba/includes/monitor_package_spec.md)

### 📋 Task Tracking
**Location:** `rtl/amba/PRD/`

- **[Tasks](../../vault/Tasks/amba/INDEX.md)** - Current work items and priorities
- **[Task Specifications](PRD/)** - Individual task details (TASK-001, etc.)

### 🐛 Known Issues
**Location:** `rtl/amba/KNOWN_ISSUES/`

- **[Known Issues Index](KNOWN_ISSUES/README.md)** - includes the FIXED transaction-table, saturation-wedge, and runtime-disable-leak issues
- Additional issue documentation as discovered

### 📖 Guides and References
- **[Configuration Guide](../../docs/user-guides/AXI_Monitor_Configuration_Guide.md)** - Monitor setup best practices
- **[README](README.md)** - Quick start and integration guide
- **[CLAUDE](CLAUDE.md)** - AI assistance guide for this subsystem

---

## 3. Protocols Supported

### 3.1 AXI4 Full Protocol
**Status:** ✅ Complete
**Modules:** `monitor/axi4_master_rd_mon.sv`, `monitor/axi4_master_wr_mon.sv`, `monitor/axi4_slave_rd_mon.sv`, `monitor/axi4_slave_wr_mon.sv`

**Features:**
- Burst transactions (1-256 beats)
- Out-of-order completion support
- Multiple outstanding transactions
- ID-based transaction tracking
- Error detection (SLVERR, DECERR, timeouts, orphans)

**Documentation:** See `docs/markdown/RTLAmba/axi4/` and `docs/markdown/RTLAmba/monitor/`

### 3.2 AXI4-Lite Protocol
**Status:** ✅ Complete
**Modules:** Dedicated `axil4_*_mon.sv` wrappers (share `axi_monitor_base`,
instantiated with `IS_AXI=0`; not the AXI4 wrappers re-parameterized)

**Features:**
- Single-beat transactions only
- Simplified interface
- Same error detection as AXI4
- Reduced resource utilization

### 3.3 APB Protocol
**Status:** ✅ Complete
**Modules:** `apb_monitor.sv`

**Features:**
- Simple peripheral bus monitoring
- Transaction tracking
- Error response detection
- Timeout detection

**Documentation:** See `docs/markdown/RTLAmba/apb/`

### 3.4 AXI-Stream Protocol
**Status:** ✅ Complete
**Modules:** `axis_master.sv`, `axis_slave.sv`

**Features:**
- Stream data monitoring
- Backpressure handling
- TKEEP/TSTRB support
- TLAST boundary detection

**Documentation:** See `docs/markdown/RTLAmba/axis4/`

---

## 4. Architecture Overview

### 4.1 Monitor + Observation Infrastructure

```
AMBA Monitor Subsystem
├── Monitor + monbus core  (rtl/amba/monitor/, 54 modules --
│   │                       monitor core, monbus infrastructure, monbus
│   │                       arbiters, and ALL protocol *_mon wrappers)
│   │
│   ├── Monitor core (13)
│   │   ├── axi_monitor_base.sv             (Top-level scaffold)
│   │   ├── axi_monitor_trans_mgr.sv        (Outstanding-txn table, pipelined
│   │   │                                    active_count for 100 MHz close)
│   │   ├── axi_monitor_addr_check.sv       (Region / address filtering)
│   │   ├── axi_monitor_filtered.sv         (Per-channel packet filtering)
│   │   ├── axi_monitor_timer.sv            (Timer + per-transaction stamps)
│   │   ├── axi_monitor_timeout.sv          (Timeout detection)
│   │   ├── axi_monitor_reporter.sv         (Packet-gen dispatcher)
│   │   ├── axi_monitor_reporter_compl.sv      (Completion packets)
│   │   ├── axi_monitor_reporter_debug.sv      (Debug)
│   │   ├── axi_monitor_reporter_error.sv      (Error)
│   │   ├── axi_monitor_reporter_perf.sv       (Performance)
│   │   ├── axi_monitor_reporter_threshold.sv  (Threshold)
│   │   ├── axi_monitor_reporter_timeout.sv    (Timeout)
│   │   └── monitor_trans_cam.sv            (CAM lookup for trans_mgr)
│   │
│   ├── Observation / performance (3)  [in rtl/amba/shared/]
│   │   ├── axi4_dma_observer.sv            (DMA observability wrapper;
│   │   │                                    AW->W AWID order tracker;
│   │   │                                    per-port latency histograms)
│   │   ├── axi_perf_latency_hist.sv        (16-bucket log2 latency histogram)
│   │   └── axi_bus_meter.sv                (4-bucket bus utilization meter)
│   │
│   ├── Monitor Bus (monbus) infrastructure (10)
│   │   ├── monbus_arbiter.sv               (Top arbitration)
│   │   ├── monbus_group_core.sv            (Shared filter+FIFO core,
│   │   │                                    used by all group wrappers)
│   │   ├── monbus_axi4_axi4_group.sv       (AXI4<->AXI4 group)
│   │   ├── monbus_axi4_axil_group.sv       (AXI4<->AXIL group)
│   │   ├── monbus_axil_axi4_group.sv       (AXIL<->AXI4, 32-bit err-drain)
│   │   ├── monbus_axil_axil_group.sv       (AXIL<->AXIL, 32-bit err-drain)
│   │   ├── monbus_compressor.sv            (mod-3 packer; cfg_compress_en)
│   │   ├── monbus_halfbeat_packer.sv       (Half-beat packer above the 66.7%
│   │   │                                    compressor ceiling)
│   │   ├── monbus_cam.sv                   (Monbus CAM)
│   │   └── monbus_cam_pipe.sv              (Pipelined CAM variant)
│   │
│   ├── Arbiters with monbus (3)
│   │   ├── arbiter_monbus_common.sv
│   │   ├── arbiter_rr_pwm_monbus.sv
│   │   └── arbiter_wrr_pwm_monbus.sv
│   │
│   ├── CDC (4)  [in rtl/amba/cdc/]
│   │   ├── cdc_2_phase_handshake.sv
│   │   ├── cdc_4_phase_handshake.sv
│   │   ├── cdc_open_loop.sv
│   │   └── cdc_synchronizer.sv
│   │
│   ├── Storage helpers (5)  [in rtl/amba/shared/; not on the monitor path]
│   │   ├── sdpram_core.sv                  (Shared FUB-shaped core)
│   │   ├── sdpram_slave_axi4_axi4.sv
│   │   ├── sdpram_slave_axi4_axil.sv
│   │   ├── sdpram_slave_axil_axi4.sv
│   │   └── sdpram_slave_axil_axil.sv
│   │
│   └── Test / utility helpers  [in rtl/amba/shared/, except
│       │                        apb_monitor_addr_check.sv in monitor/]
│       ├── axi4_dma_slaves.sv              (Bundled slave wrapper for DMA TB)
│       ├── axi4_slave_rd_pattern_gen.sv    (Pattern source)
│       ├── axi4_slave_wr_crc_check.sv      (CRC sink)
│       ├── axi_master_rd_splitter.sv
│       ├── axi_master_wr_splitter.sv
│       ├── axi_split_combi.sv
│       ├── axi_gen_addr.sv
│       ├── amba_clock_gate_ctrl.sv
│       └── apb_monitor_addr_check.sv
│
├── AXI4 Monitors (rtl/amba/monitor/, 8 files)
│   ├── axi4_master_rd_mon.sv  / _cg.sv     (Master read + clock-gated)
│   ├── axi4_master_wr_mon.sv  / _cg.sv
│   ├── axi4_slave_rd_mon.sv   / _cg.sv
│   └── axi4_slave_wr_mon.sv   / _cg.sv
│       (the non-monitor axi4_{master,slave}_{rd,wr}.sv base wrappers
│        stay in rtl/amba/axi4/)
│
├── AXI4-Lite Monitors (rtl/amba/monitor/, 8 files)
│   └── axil4_*_mon.sv (+ _cg)              Dedicated wrappers --
│                                           NOT axi4_*_mon with IS_AXI=0.
│                                           Share axi_monitor_base + packet
│                                           format with AXI4 monitors.
│                                           (bases in rtl/amba/axil4/)
│
├── AXI5 / APB / APB5 monitors (rtl/amba/monitor/) over bases in
│   rtl/amba/axi5/, apb/, apb5/; AXI-Stream in rtl/amba/axis*/
│
└── (Removed/superseded)
    ├── mon_temp/ legacy trans_mgr           Deleted in d246a72d
    └── unified sdpram_slave.sv              Replaced by sdpram_core +
                                             4 protocol-pair wrappers
```

**Notable refactors landed in 2026:**

| Commit | Change |
|---|---|
| `5de2b761` | `axi4_dma_observer`: per-channel AW→W AWID order tracker, no sideband |
| `5be0a63b` | `axi4_dma_observer`: per-port latency histograms (parity with in-core) |
| `6865935a` | RFC perfmon Stage E option 2: in-core datapath R/W perf monitors + arm-gap fix |
| `da4529b3` / `abb929a6` | 32-bit AXIL err-drain on `monbus_axil_axi4_group` / `monbus_axil_axil_group` |
| `61edda71` | `monbus_compressor` mod-3 refactor + shared `monbus_group.f` + compressor input skid |
| `665057f9` | Runtime `cfg_compress_en` on monbus groups |
| `2554219b` | Synchronous CAM-clear config bit (`CTRL[4]`) |
| `d246a72d` | Deleted legacy `mon_temp/` `trans_mgr` + equivalence test |
| `cb29e226` | Saturation-recovery contract: command-entry cap + strict `block_ready` reopen margin (`monitor_common_pkg::cmd_entry_reserve`), stray non-last-beat absorption, timeout coverage holes closed; formal made discriminating |
| `95c9490a` | Runtime-disable auto-retire (reporter), same-cycle AW+W bypass (trans_mgr), wrapper API wired live (`cfg_monitor_enable` master gate, `cfg_timeout_cycles`, `ACTIVE_TRANS_THRESHOLD`, `error_count`/`transaction_count`), AXI5 W-channel wiring fixed |
| `b514d8cd` / `1c016603` / `fd2d4f29` | Monbus group sources via shared `monbus_group.f` filelist (stream / rapids / bridge) |

**See:** `docs/markdown/RTLAmba/overview.md` for detailed architecture, and `rtl/amba/PRD/RFCs/RFC-perfmon-window-buckets.md` for the windowed-perfmon design.

### 4.2 Monitor Bus Protocol

All monitors output the standardized 128-bit `monitor_packet_t`
(`monitor_common_pkg.sv`), paired with a 64-bit side-band timestamp
(`monbus_timestamp_t`) sampled at emission time:

- **[127:124]** Packet type (error, completion, threshold, timeout, perf,
  perfwin, perfhist, debug, ...)
- **[123:109]** Reserved (15 bits, forward-compat slack)
- **[108:105]** Protocol identifier (AXI/AXIS/APB/ARB/CORE)
- **[104:97]** Event code (8 bits, protocol-specific)
- **[96:88]** Channel ID (9 bits; AXI ID or channel index)
- **[87:72]** Agent ID (16 bits)
- **[71:64]** Unit ID (8 bits)
- **[63:0]** Event-specific data (64 bits; full 64-bit address, latency,
  counter value, etc.)

Neither width is a per-module parameter: `MONBUS_PKT_WIDTH = 128` and
`MONBUS_TS_WIDTH = 64` are locked in `monitor_common_pkg`.

**See:** `docs/markdown/RTLAmba/includes/monitor_package_spec.md`

---

## 5. Key Features

### 5.1 Transaction Monitoring

| Feature | Status | Description |
|---------|--------|-------------|
| Concurrent tracking | ✅ | Up to MAX_TRANSACTIONS outstanding |
| Out-of-order completion | ✅ | ID-based matching |
| Burst support | ✅ | 1-256 beats, all types |
| Orphan detection | ✅ | Data/response without command |

### 5.2 Error Detection

| Error Type | Detection | Status |
|------------|-----------|--------|
| SLVERR response | ✅ | Slave error |
| DECERR response | ✅ | Decode error |
| Command timeout | ✅ | Configurable threshold |
| Data timeout | ✅ | Configurable threshold |
| Response timeout | ✅ | Configurable threshold |
| Protocol violations | ✅ | Orphan data/response |

### 5.3 Performance Metrics

| Metric | Support | Status |
|--------|---------|--------|
| Transaction latency | ✅ | Cycle-accurate |
| Active transaction count | ✅ | Real-time |
| Completion rate | ✅ | Transactions/cycle |
| Threshold detection | ✅ | Configurable limits |

### 5.4 Configuration

| Feature | Status | Notes |
|---------|--------|-------|
| Runtime enable/disable | ✅ | Per packet type |
| Timeout thresholds | ✅ | Per transaction phase |
| Packet filtering | ✅ | Prevent bus congestion |
| Clock gating support | ✅ | Power optimization |

---

## 6. Verification Architecture

### 6.1 MANDATORY: Testbench Reusability Requirements

**⚠️ CRITICAL REQUIREMENT - NO EXCEPTIONS ⚠️**

All AMBA verification components MUST follow this architecture to enable reuse across dozens of test scenarios and integration points.

**Required Structure:**

```
bin/TBClasses/[protocol]/
    ├── [module]_tb.py           ← REUSABLE TESTBENCH CLASS
    ├── [module]_scoreboard.py   ← REUSABLE SCOREBOARD (if needed)
    ├── [module]_packets.py      ← REUSABLE PACKET TYPES (if needed)
    └── [module]_config.py       ← REUSABLE CONFIG (if needed)

val/amba/
    └── test_[module].py          ← TEST RUNNER ONLY (imports TB)
```

**Testbench Class Location:**
- ✅ **MUST BE:** `bin/TBClasses/[protocol]/[module]_tb.py`
- ❌ **NEVER:** Embedded in `val/amba/test_*.py` files

**Test Runner Responsibilities (ONLY):**
1. Import testbench class from `bin/TBClasses/`
2. Define pytest parameters and test matrix
3. Configure RTL sources and compilation
4. Call `cocotb_test.simulator.run()`

**Testbench Class Responsibilities:**
1. DUT initialization and configuration
2. Clock and reset management
3. Transaction generation and monitoring
4. Scoreboarding and checking
5. Reusable test sequences

**Why This Matters:**

The same testbench will be used in:
- Unit tests (`val/amba/`)
- Integration tests (`val/integ_amba/`)
- Project/system tests (`projects/components/*/dv/tests/`)
- User project imports (external reuse)
- CI/CD regression suites

**If testbench is embedded in test file, it is WORTHLESS for reuse!**

**Example - CORRECT Pattern:**

```python
# bin/TBClasses/axi4/axi4_master_read_tb.py
class AXI4MasterReadTB(TBBase):
    """Reusable testbench for AXI4 master read validation"""

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        # Initialize

    async def run_basic_test(self):
        # Test logic

# val/amba/test_axi4_master_rd.py (TEST RUNNER ONLY)
from TBClasses.axi4.axi4_master_read_tb import AXI4MasterReadTB

@cocotb.test()
async def axi4_master_read_test(dut):
    tb = AXI4MasterReadTB(dut)  # ← Import and use
    await tb.setup_clocks_and_reset()
    await tb.run_basic_test()

@pytest.mark.parametrize("aw, dw, ...", ...)
def test_axi4_master_read(request, aw, dw, ...):
    # Only pytest runner logic, RTL sources, run() call
    run(verilog_sources=..., module=module, ...)
```

**Verification Checklist:**

Before submitting any test:
- [ ] Testbench class exists in `bin/TBClasses/[protocol]/`
- [ ] Test runner imports testbench (does not define it)
- [ ] Testbench has no test-specific hardcoded values
- [ ] Testbench can be imported and reused by other tests
- [ ] Test runner only handles pytest params and compilation

**Reference Examples:**
- `bin/TBClasses/axi4/axi4_master_read_tb.py`
- `bin/TBClasses/apb_monitor/apb_monitor_core_tb.py`
- `bin/TBClasses/axi4/monitor/axi_monitor_config_tb.py`

**See Also:**
- `CLAUDE.md` Rule #0 for detailed AI assistance guidance
- Existing AMBA tests in `val/amba/` for working examples

---

## 7. Test Coverage

### 7.1 Current Status

**val/amba regression (as of `95c9490a`):** 679 passed / 0 failed.
Monitor formal: 10/10 proof directories PASS (in-RTL properties,
mutation-checked).

| Test Scenario | Status | Notes |
|---------------|--------|-------|
| Basic Transactions | ✅ PASS | Completions tracked |
| Burst Transactions | ✅ PASS | Beat counting |
| Outstanding Transactions | ✅ PASS | Concurrent + same-ID slots |
| ID Reordering | ✅ PASS | Oldest-first attribution |
| Backpressure | ✅ PASS | Handshake stalls |
| Timeout Detection | ✅ PASS | Incl. cmd-accepted / first-beat-missing |
| Error Responses | ✅ PASS | |
| Orphan Detection | ✅ PASS | |
| Saturation recovery | ✅ PASS | `test_axi_monitor_trans_mgr.py` + 100-seed undersized stream sweep |
| Runtime-disable / auto-retire | ✅ PASS | `test_axi_monitor_runtime_disable.py` |
| Same-cycle AW+W | ✅ PASS | `test_axi_monitor_wr_same_cycle.py` |

**Verification Location:** `val/amba/`

### 6.2 Coverage Goals

- **Functional:** >95% ✅ (achieved)
- **Code:** >90% ⏳ (~85% current)
- **Corner Cases:** 100% ✅ (explicit tests)

---

## 7. Known Issues Summary

### 7.1 Resolved Issues

**✅ ISSUE-001: Transaction Table Exhaustion (FIXED 2025-09-30)**
- **Description:** Missing event_reported feedback between reporter and trans_mgr
- **Impact:** Transactions never cleaned up, monitor stopped after MAX_TRANSACTIONS
- **Fix:** Added feedback wire, verified in TASK-001
- **Documentation:** `KNOWN_ISSUES/README.md` (Issue #0, event_reported feedback)

**✅ Multi-channel saturation wedge (FIXED, `cb29e226`)**
- Stray non-last data beats poisoned terminal entries into an unclosable
  state; occupancy pinned at MAX and the flat `block_ready` margin placed
  the reopen threshold exactly at the fill point — permanent stall of the
  monitored datapath. Fixed by the saturation-recovery contract
  (`monitor_common_pkg::cmd_entry_reserve`).
- **Documentation:** `KNOWN_ISSUES/axi_monitor_blockready_hang_partial_channels.md`

**✅ Runtime-disable slot leak / dead wrapper API / same-cycle AW+W /
AXI5 W wiring (FIXED, `95c9490a`)**
- Runtime-disabled packet classes now auto-retire terminal entries;
  `cfg_monitor_enable`, `cfg_timeout_cycles`, `ACTIVE_TRANS_THRESHOLD`,
  `error_count`/`transaction_count` are live on all 12 wrappers; write
  monitors capture AW+W presented in the same cycle; AXI5 write monitors
  use the AWID/2'b00 W-channel convention.

**✅ active_count underflow (FIXED)**
- The alloc-minus-cleanup accumulator could underflow to 0xFF under legal
  AXI (found by SymbiYosys); replaced with a registered pop-count of CAM
  occupancy. See `KNOWN_ISSUES/axi_monitor_active_count_underflow.md`.

### 7.2 Open Issues

**⚠️ 8-channel STREAM engine wedge (non-monitor)**
- A residual hang in the 8-channel stream-engine stress family
  (params 7/9/11 of the multi-channel sweep) persists after the monitor
  fixes — the mechanism is in the DMA engine side, not the monitor path.
  Tracked in the STREAM project area.

**⚠️ axil4 monitor TB drain-window race (framework, non-RTL)**
- The 8 axil4 monitor suites shared a drain-window race with the trans_mgr
  suite; seeds are pinned as an interim workaround (`95c9490a`). The
  proper settle-poll fix belongs in the RDS-DV (CocoTBFramework) repo.

**See:** `KNOWN_ISSUES/` for detailed issue tracking

---

## 8. Integration Guidelines

### 8.1 Quick Start

```systemverilog
// Example: AXI4 Master Read Monitor
axi4_master_rd_mon #(
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),
    .MAX_TRANSACTIONS(16)
) u_axi_mon (
    .aclk               (axi_clk),
    .aresetn            (axi_rst_n),

    // AXI4 Read Address Channel
    .axi_arid           (m_axi_arid),
    .axi_araddr         (m_axi_araddr),
    .axi_arvalid        (m_axi_arvalid),
    .axi_arready        (m_axi_arready),

    // AXI4 Read Data Channel
    .axi_rid            (m_axi_rid),
    .axi_rdata          (m_axi_rdata),
    .axi_rvalid         (m_axi_rvalid),
    .axi_rready         (m_axi_rready),
    .axi_rlast          (m_axi_rlast),

    // Monitor Bus Output (128-bit packet + 64-bit side-band timestamp)
    .monbus_valid       (mon_valid),
    .monbus_ready       (mon_ready),
    .monbus_packet      (mon_packet),
    .monbus_timestamp   (mon_timestamp),

    // Configuration
    .cfg_monitor_enable (1'b1),   // master gate: 0 = monitor inert
    .cfg_error_enable   (1'b1),
    .cfg_compl_enable   (1'b1),
    .cfg_timeout_enable (1'b1)
);
```

**See:** `README.md` for more integration examples

### 8.2 Configuration Best Practices

**⚠️ IMPORTANT:** Avoid enabling all packet types simultaneously — the
monitor bus sustains at most one packet per two cycles and will congest.

**Mode 1: Functional Debug (Recommended)**
```systemverilog
cfg_error_enable    = 1
cfg_compl_enable    = 1
cfg_timeout_enable  = 1
cfg_perf_enable     = 0  // Disable to avoid congestion
```

**Mode 2: Performance Analysis**
```systemverilog
cfg_error_enable    = 1
cfg_compl_enable    = 0  // Runtime-disable: safe since 95c9490a
cfg_timeout_enable  = 0
cfg_perf_enable     = 1
```

Runtime-disabling a class is safe: since `95c9490a` the reporter
auto-retires terminal entries of disabled classes (no packet, no counter
bump), so the table cannot leak and `block_ready` cannot wedge. Before
that commit Mode 2 wedged the monitored bus after ~MAX_TRANSACTIONS
transactions. To keep counting while suppressing emission, use
`cfg_axi_pkt_mask` (drop mask in `axi_monitor_filtered`) instead of the
runtime disable.

**See:** `docs/user-guides/AXI_Monitor_Configuration_Guide.md` for detailed configuration strategies

---

## 9. Development Status

### 9.1 Current Phase

**Phase 3: Validation and Bug Fixing** (In Progress)

- ✅ Core monitor infrastructure complete
- ✅ Transaction tracking operational
- ✅ Error detection working
- ✅ Critical bug fixed (event_reported feedback)
- ⏳ Test configuration refinement
- ⏳ Performance characterization

**See:** `/vault/Tasks/amba/` for detailed task breakdown

### 9.2 Roadmap

**Completed since the original roadmap:**
- Test configuration issues fixed (val/amba fully green)
- Address filtering (`N_ADDR_RANGES` range checker) and AXI5 wrappers landed
- Formal property checking landed (in-RTL properties, mutation-checked,
  10/10 proof directories)

**Remaining:**
- Complete performance characterization (perfmon RFC Stages C/D/F)
- Integration examples and guides
- Root-cause the non-monitor 8-channel STREAM engine wedge (see 7.2)

---

## 10. Performance Characteristics

### 10.1 Resource Utilization

**Target:** <2% area overhead per monitored interface

**Actual:** (Characterization pending)
- Monitor logic: Minimal combinational
- Transaction table: Depends on MAX_TRANSACTIONS
- FIFO buffers: Configurable depth

### 10.2 Timing

**Target:** Support up to 1 GHz operation (technology dependent)

**Critical Paths:**
- Transaction lookup: O(MAX_TRANSACTIONS) comparisons
- Packet generation: Pipelined in reporter
- Monitor bus output: Buffered via FIFO

**Optimization:** Use clock-gated variants (*_cg.sv) for power-sensitive designs

---

## 11. Verification Infrastructure

### 11.1 Test Files

**Location:** `val/amba/`

**Key Test Files:**
- `test_axi4_monitor.py` - Comprehensive AXI monitor validation (8 scenarios)
- `test_apb_monitor.py` - APB protocol monitoring
- `test_axis_master.py` - AXIS master interface
- `test_axis_slave.py` - AXIS slave interface
- `test_axi4_*_mon.py` - Individual monitor wrappers
- `test_axi4_matrix_integration.py` - System-level integration

### 11.2 CocoTB Framework

**Location:** `bin/TBClasses/amba/`

**Components:**
- Monitor testbenches
- Arbiter test infrastructure
- Random configuration generators
- Clock gating control

**Documentation:** See `docs/markdown/TBClasses/amba/`

---

## 12. Quick Reference

### 12.1 Key Files

| File | Purpose |
|------|---------|
| `rtl/amba/PRD.md` | This document (high-level overview) |
| `rtl/amba/README.md` | Quick start and integration guide |
| `rtl/amba/CLAUDE.md` | AI assistance guide |
| `/vault/Tasks/amba/` | Current work items |
| `rtl/amba/KNOWN_ISSUES/` | Bug tracking |
| `docs/markdown/RTLAmba/` | **Detailed RTL documentation** |
| `docs/user-guides/AXI_Monitor_Configuration_Guide.md` | Configuration best practices |

### 12.2 Commands

```bash
# Run all AMBA tests
pytest val/amba/ -v

# Run specific monitor test
pytest val/amba/test_axi4_monitor.py -v

# Lint monitor RTL
verilator --lint-only rtl/amba/monitor/axi_monitor_base.sv

# View detailed docs
cat docs/markdown/RTLAmba/index.md
```

---

## 13. Success Criteria

### 13.1 Functional

- ✅ All monitor packet types generated correctly
- ✅ Transaction table cleanup working (event_reported fixed)
- ✅ ID reuse operational
- ⏳ 8/8 comprehensive tests passing (currently 6/8)

### 13.2 Quality

- ✅ Zero critical RTL bugs
- ✅ >95% functional coverage
- ⏳ >90% code coverage (currently ~85%)
- ✅ Verilator compiles with 0 warnings

### 13.3 Documentation

- ✅ Configuration guide complete
- ✅ Known issues documented with workarounds
- ✅ Detailed RTL specs in docs/markdown/RTLAmba/
- ⏳ Integration guide (in progress)

---

## 14. References

### 14.1 Internal Documentation

- **Detailed RTL Specs:** `docs/markdown/RTLAmba/` ← **Primary technical reference**
- **Test Framework:** `docs/markdown/TBClasses/amba/`
- **Configuration:** `docs/user-guides/AXI_Monitor_Configuration_Guide.md`
- **Validation Report:** `projects/components/dmas/rapids/docs/RAPIDS_Validation_Status_Report.md`
- **Master PRD:** `/PRD.md`
- **Repository Guide:** `/CLAUDE.md`

### 14.2 External References

- **AMBA Specifications:**
  - AXI4: ARM IHI0022E
  - APB: ARM IHI0024C
  - AXI-Stream: ARM IHI0051A
- **Tools:**
  - CocoTB: https://docs.cocotb.org/
  - Verilator: https://verilator.org/

---

**Document Version:** 1.0
**Last Updated:** 2025-09-30
**Review Cycle:** Monthly during active development
**Next Review:** 2025-10-30
**Owner:** RTL Design Sherpa Project

---

## Navigation

- **← Back to Root:** `/PRD.md`
- **Detailed RTL Docs:** `docs/markdown/RTLAmba/`
- **Quick Start:** `README.md`
- **AI Guidance:** `CLAUDE.md`
- **Tasks:** `/vault/Tasks/amba/`
- **Issues:** `KNOWN_ISSUES/`
