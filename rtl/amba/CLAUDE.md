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

## Critical Rules for This Subsystem

### Rule #0: VERIFICATION ARCHITECTURE - MANDATORY COMPLIANCE

**⚠️ HIGH PRIORITY: All AMBA testbenches MUST follow the standardized verification architecture ⚠️**

**Complete Guide:** `docs/VERIFICATION_ARCHITECTURE_GUIDE.md` ← **READ THIS FIRST**

**NEVER embed testbench classes inside test runner files!** The testbench code will be instantiated in DOZENS of places across the project. Having testbench logic only in test files makes it COMPLETELY WORTHLESS for reuse.

**MANDATORY Structure:**

```
bin/CocoTBFramework/tbclasses/
├── axi4/
│   ├── axi4_master_read_tb.py      ← REUSABLE TB CLASS
│   ├── axi4_master_write_tb.py     ← REUSABLE TB CLASS
│   └── monitor/
│       └── axi_monitor_config_tb.py ← REUSABLE TB CLASS
├── apb_monitor/
│   ├── apb_monitor_core_tb.py      ← REUSABLE TB CLASS
│   ├── apb_monitor_scoreboard.py   ← REUSABLE COMPONENTS
│   └── apb_monitor_packets.py      ← REUSABLE COMPONENTS
└── [protocol]/
    └── [module]_tb.py               ← REUSABLE TB CLASS

val/amba/
├── test_axi4_master_rd.py          ← TEST RUNNER ONLY (imports TB)
├── test_apb_monitor.py             ← TEST RUNNER ONLY (imports TB)
└── test_*.py                        ← TEST RUNNER ONLY (imports TB)
```

**Test Runner Pattern (CORRECT):**
```python
# val/amba/test_axi4_master_rd.py
from CocoTBFramework.tbclasses.axi4.axi4_master_read_tb import AXI4MasterReadTB

@cocotb.test()
async def axi4_master_read_test(dut):
    """Test runner - imports TB, runs test"""
    tb = AXI4MasterReadTB(dut)  # ← TB imported from tbclasses/
    await tb.setup_clocks_and_reset()
    await tb.run_basic_test()

@pytest.mark.parametrize("aw, dw, ...", generate_test_params())
def test_axi4_master_read(request, aw, dw, ...):
    """Pytest runner - only handles parameters and run()"""
    # ... RTL sources, parameters, etc ...
    run(verilog_sources=..., module=module, ...)
```

**Testbench Class Pattern (CORRECT):**
```python
# bin/CocoTBFramework/tbclasses/axi4/axi4_master_read_tb.py
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

class AXI4MasterReadTB(TBBase):
    """Reusable testbench for AXI4 master read validation"""

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        # TB initialization

    async def setup_clocks_and_reset(self):
        # Clock/reset logic

    async def run_basic_test(self):
        # Test logic
```

**Why This Matters:**

1. **Reusability**: Same TB class used in:
   - Unit tests (`val/amba/test_*.py`)
   - Integration tests (`val/system/test_*.py`)
   - System-level tests (`val/soc/test_*.py`)
   - User projects (external imports)

2. **Maintainability**: Fix bug once in TB class, all tests benefit

3. **Composition**: TB classes can inherit/compose:
   ```python
   class AXI4MasterReadCGTB(AXI4MasterReadTB):
       """Extends base TB with clock gating support"""
   ```

4. **Discoverability**: Users can find and import TB classes

**❌ WRONG - Testbench Embedded in Test File:**
```python
# val/amba/test_axi4_monitor.py - WRONG!
class AXI4MonitorTB(TBBase):  # ← TB class in test file!
    # 500 lines of TB logic...

@cocotb.test()
async def axi4_monitor_test(dut):
    tb = AXI4MonitorTB(dut)  # ← Can't be imported by other tests!
```

**✅ CORRECT - Separate TB Class:**
```python
# bin/CocoTBFramework/tbclasses/axi4/monitor/axi_monitor_tb.py
class AXIMonitorTB(TBBase):
    # 500 lines of REUSABLE TB logic...

# val/amba/test_axi4_monitor.py
from CocoTBFramework.tbclasses.axi4.monitor.axi_monitor_tb import AXIMonitorTB

@cocotb.test()
async def axi4_monitor_test(dut):
    tb = AXIMonitorTB(dut)  # ← Imported, reusable!
```

**Three-Layer Pattern (MANDATORY):**
1. **Testbench (TB)**: `bin/CocoTBFramework/tbclasses/amba/{module}_tb.py` - Infrastructure + BFMs
2. **Scoreboard**: `bin/CocoTBFramework/scoreboards/amba/{module}_scoreboard.py` - Verification logic
3. **Test**: `val/amba/test_{module}.py` - Test intelligence (imports TB)

**Verification Method Selection:**
- ✅ **Use Queue Access** for: APB monitors, simple control paths, in-order transactions
- ✅ **Use Memory Models** for: Multi-master AXI, out-of-order scenarios, data integrity checks

**When Creating New Tests:**

1. ✅ **FIRST**: Create TB class in `bin/CocoTBFramework/tbclasses/[protocol]/`
2. ✅ **SECOND**: Create scoreboard in `bin/CocoTBFramework/scoreboards/[protocol]/`
3. ✅ **THIRD**: Create test runner in `val/amba/` that imports TB
4. ❌ **NEVER**: Put TB class or verification logic directly in test file

**Verification Checklist:**
- [ ] TB class exists in `bin/CocoTBFramework/tbclasses/`
- [ ] Scoreboard exists in `bin/CocoTBFramework/scoreboards/`
- [ ] Test runner imports TB class (not defines it)
- [ ] TB class contains only infrastructure (no verification logic)
- [ ] Scoreboard contains all verification logic
- [ ] Appropriate verification method used (queue access vs memory model)
- [ ] Test runner only handles pytest params and `run()` call

**📖 Complete Documentation:**
- **`docs/VERIFICATION_ARCHITECTURE_GUIDE.md`** - Full guide with AMBA examples
- `PRD.md` Section 4.4 - Architecture overview with decision tree
- `bin/CocoTBFramework/CLAUDE.md` - Framework verification patterns

**Action Required:** All new tests must follow this pattern. Existing tests should be migrated (see migration guide in VERIFICATION_ARCHITECTURE_GUIDE.md).

---

### Rule #1: Always Reference Detailed Documentation

**This subsystem has extensive documentation in** `docs/markdown/RTLAmba/`

**Before answering technical questions:**
```bash
# Check detailed docs first
ls docs/markdown/RTLAmba/
cat docs/markdown/RTLAmba/overview.md
cat docs/markdown/RTLAmba/axi/axi4_master_rd.md
```

**Your answer should:**
1. Provide direct answer/code
2. **Then link to detailed docs:** "See `docs/markdown/RTLAmba/{file}.md` for complete specification"

### Rule #2: NEVER Enable All Monitor Packet Types

**This is the #1 integration mistake!**

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

**Always say:** "⚠️ Never enable completions + performance simultaneously!"
**Always link:** "See `docs/AXI_Monitor_Configuration_Guide.md` for configuration strategies"

### Rule #3: Know the Known Issues

**Current Status:**
- ✅ **Event reported feedback bug FIXED** (2025-09-30)
- ⚠️ **2 test failures** (test configuration, NOT RTL bugs)

**Always check:** `rtl/amba/KNOWN_ISSUES/` before diagnosing bugs

```bash
ls rtl/amba/KNOWN_ISSUES/
cat rtl/amba/KNOWN_ISSUES/axi_monitor_reporter.md
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
    .monbus_pkt_valid (mon_valid),
    .monbus_pkt_data  (mon_data),
    .monbus_pkt_ready (1'b1)  // ❌ Always ready = packet loss risk!
);
```

**Complete example:**
```systemverilog
✅ COMPLETE:
// Monitor
axi4_master_rd_mon u_mon (
    // ... AXI signals ...
    .monbus_pkt_valid (mon_valid),
    .monbus_pkt_data  (mon_data),
    .monbus_pkt_ready (fifo_ready)
);

// Downstream FIFO
gaxi_fifo_sync #(.DATA_WIDTH(64), .DEPTH(256)) u_fifo (
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
| `axi4_master_rd_mon.sv` | Master read monitoring | ID_WIDTH, ADDR_WIDTH, DATA_WIDTH, MAX_TRANSACTIONS | `docs/markdown/RTLAmba/axi/axi4_master_rd.md` |
| `axi4_master_wr_mon.sv` | Master write monitoring | Same | `docs/markdown/RTLAmba/axi/` |
| `axi4_slave_rd_mon.sv` | Slave read monitoring | Same | `docs/markdown/RTLAmba/axi/` |
| `axi4_slave_wr_mon.sv` | Slave write monitoring | Same | `docs/markdown/RTLAmba/axi/` |
| `*_cg.sv` variants | Clock-gated versions | Same + CG_ENABLE | Power optimization |

### APB Monitors

| Module | Purpose | Key Params | Documentation |
|--------|---------|------------|---------------|
| `apb_monitor.sv` | APB transaction monitoring | ADDR_WIDTH, DATA_WIDTH, MAX_TRANSACTIONS | `docs/markdown/RTLAmba/apb/` |

### AXIS Monitors

| Module | Purpose | Key Params | Documentation |
|--------|---------|------------|---------------|
| `axis_master.sv` | AXIS transmit monitoring | DATA_WIDTH, ID_WIDTH, DEST_WIDTH | `docs/markdown/RTLAmba/fabric/axis_master.md` |
| `axis_slave.sv` | AXIS receive monitoring | Same | `docs/markdown/RTLAmba/fabric/` |

### Supporting Infrastructure

| Module | Purpose | Location |
|--------|---------|----------|
| `axi_monitor_base.sv` | Core monitor logic | `rtl/amba/shared/` |
| `axi_monitor_trans_mgr.sv` | Transaction tracking | `rtl/amba/shared/` |
| `axi_monitor_reporter.sv` | Packet generation | `rtl/amba/shared/` |
| `axi_monitor_timeout.sv` | Timeout detection | `rtl/amba/shared/` |
| `arbiter_*_monbus.sv` | Monitor bus arbitration | `rtl/amba/shared/` |

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
    .monbus_pkt_valid (mon_valid),
    .monbus_pkt_ready (mon_ready),
    .monbus_pkt_data  (mon_data),
    // Configuration
    .cfg_error_enable   (1'b1),
    .cfg_compl_enable   (1'b1),
    .cfg_timeout_enable (1'b1),
    .cfg_perf_enable    (1'b0)  // ⚠️ Disable to avoid congestion
);

// Add downstream FIFO
gaxi_fifo_sync #(.DATA_WIDTH(64), .DEPTH(256)) u_fifo (
    .i_clk(axi_clk), .i_rst_n(axi_rst_n),
    .i_valid(mon_valid), .i_data(mon_data), .o_ready(mon_ready),
    // ... connect to your packet consumer
);
```

**Then link:**
- **Integration:** See `rtl/amba/README.md` for complete examples
- **Configuration:** See `docs/AXI_Monitor_Configuration_Guide.md`
- **Module spec:** See `docs/markdown/RTLAmba/axi/axi4_master_rd.md`

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

**📖 See:** `docs/AXI_Monitor_Configuration_Guide.md` (comprehensive guide)

### Q: "Monitor packets format?"

**A: 64-bit standardized format:**
```
[63:60] Packet Type  (0=ERROR, 1=COMPL, 2=TIMEOUT, 3=THRESH, 4=PERF, 5=DEBUG)
[59:57] Protocol     (0=AXI, 1=APB, 2=AXIS)
[56:53] Event Code
[52:47] Channel ID
[46:43] Unit ID
[42:35] Agent ID
[34:0]  Event Data   (address, latency, error info, etc.)
```

**Decode example:**
```systemverilog
logic [3:0] pkt_type   = monbus_pkt_data[63:60];
logic [2:0] protocol   = monbus_pkt_data[59:57];
logic [34:0] event_data = monbus_pkt_data[34:0];
```

**📖 See:** `docs/markdown/RTLAmba/includes/monitor_package_spec.md` (complete spec)

### Q: "How to handle multiple monitors?"

**A: Use arbiter to aggregate:**
```systemverilog
// Multiple monitors
wire [N-1:0] mon_valid;
wire [N-1:0][63:0] mon_data;
wire [N-1:0] mon_ready;

// Arbiter aggregates packets
arbiter_rr_monbus #(
    .N(N),
    .DATA_WIDTH(64)
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
gaxi_fifo_sync #(.DATA_WIDTH(64), .DEPTH(1024)) u_agg_fifo (
    .i_valid (agg_valid),
    .i_data  (agg_data),
    // ... to system consumer
);
```

### Q: "What's MAX_TRANSACTIONS?"

**A: Transaction table size:**
- Tracks up to MAX_TRANSACTIONS concurrent transactions
- Must be >= maximum outstanding transactions on bus
- **Typical values:**
  - AXI4: 16-32 (supports burst, out-of-order)
  - AXI4-Lite: 4-8 (single-beat only)
  - APB: 2-4 (simple protocol)

**If too small:**
- Monitor logs warning
- New transactions blocked until slots free
- Recent fix ensures proper cleanup (event_reported feedback)

**Recommendation:** "Use 16-32 for AXI4, can reduce for simpler protocols"

### Q: "Why are tests failing?"

**A: Check current status first:**

```bash
# View test results
pytest val/amba/test_axi_monitor.py -v
```

**Current Known Issues:**
- ✅ **Event reported bug:** FIXED (2025-09-30)
- ⚠️ **2 test failures:** Test configuration issues (NOT RTL bugs)
  - Error response test expects different packet type
  - Orphan detection test configuration mismatch
  - **RTL works correctly**, tests need adjustment

**If user reports test failure:**
1. Check `rtl/amba/KNOWN_ISSUES/` for documented issues
2. Run test with `-v -s` for verbose output
3. Check if it's a known test configuration issue

**📖 See:** `rtl/amba/KNOWN_ISSUES/axi_monitor_reporter.md`

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
    .monbus_pkt_valid(mon_valid),
    .monbus_pkt_ready(mon_ready),
    .monbus_pkt_data(mon_data),
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
    .monbus_pkt_valid(mon_valid),
    .monbus_pkt_ready(mon_ready),
    .monbus_pkt_data(mon_data),
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
    .monbus_pkt_valid(mon_valid),
    .monbus_pkt_data(mon_data)
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
See docs/AXI_Monitor_Configuration_Guide.md"
```

### ❌ Anti-Pattern 2: No Downstream Handling

```systemverilog
❌ WRONG:
assign monbus_pkt_ready = 1'b1;  // Always ready

✅ CORRECTED:
"Connect to FIFO or proper consumer:
gaxi_fifo_sync #(.DATA_WIDTH(64), .DEPTH(256)) u_fifo (
    .i_valid(monbus_pkt_valid),
    .i_data(monbus_pkt_data),
    .o_ready(monbus_pkt_ready),
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
pytest val/amba/test_axi_monitor.py -v -s  # Verbose test
pytest val/amba/test_axi_monitor.py --vcd=debug.vcd
gtkwave debug.vcd
```

### Issue: Test Failures

**Check known issues:**
```bash
ls rtl/amba/KNOWN_ISSUES/
cat rtl/amba/KNOWN_ISSUES/axi_monitor_reporter.md
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
pytest val/amba/test_axi_monitor.py -v

# All AMBA tests
pytest val/amba/ -v

# Specific protocol
pytest val/amba/test_apb_monitor.py -v

# With waveforms
pytest val/amba/test_axi_monitor.py --vcd=waves.vcd
gtkwave waves.vcd
```

### Test Status (Current)

**AXI Monitor:** 6/8 passing
- ✅ Basic (5/5)
- ✅ Burst (6/6)
- ✅ Outstanding (7/7)
- ✅ ID reorder (4/4)
- ✅ Backpressure
- ✅ Timeout
- ⚠️ Error response (test config)
- ⚠️ Orphan (test config)

---

## Key Documentation Links

### Always Reference These

**Primary Technical Docs:**
- `docs/markdown/RTLAmba/index.md` - Module index
- `docs/markdown/RTLAmba/overview.md` - Architecture
- `docs/markdown/RTLAmba/axi/` - AXI module specs
- `docs/markdown/RTLAmba/apb/` - APB module specs
- `docs/markdown/RTLAmba/fabric/` - AXIS module specs
- `docs/markdown/RTLAmba/includes/monitor_package_spec.md` - Packet format

**Configuration:**
- `docs/AXI_Monitor_Configuration_Guide.md` ← **Essential for correct setup**

**This Subsystem:**
- `rtl/amba/PRD.md` - Requirements overview
- `rtl/amba/README.md` - Quick start guide
- `rtl/amba/PRD/TASKS.md` - Current work
- `rtl/amba/KNOWN_ISSUES/` - Bug tracking

**Root:**
- `/PRD.md` - Master requirements
- `/CLAUDE.md` - Repository guide

---

## Quick Commands

```bash
# View detailed docs
cat docs/markdown/RTLAmba/overview.md
cat docs/markdown/RTLAmba/axi/axi4_master_rd.md

# Check configuration guide
cat docs/AXI_Monitor_Configuration_Guide.md

# Run tests
pytest val/amba/test_axi_monitor.py -v

# Check known issues
ls rtl/amba/KNOWN_ISSUES/
cat rtl/amba/KNOWN_ISSUES/axi_monitor_reporter.md

# Lint
verilator --lint-only rtl/amba/shared/axi_monitor_base.sv
```

---

## Remember

1. 📖 **Link to detailed docs** - `docs/markdown/RTLAmba/` has complete specs
2. ⚠️ **Configuration critical** - Never all packet types together
3. 🐛 **Check known issues** - Before diagnosing bugs
4. 🔗 **Complete integration** - Monitor + config + downstream handling
5. ✅ **Test awareness** - 6/8 passing, 2 config issues (non-RTL)

---

**Version:** 1.0
**Last Updated:** 2025-09-30
**Maintained By:** RTL Design Sherpa Project
