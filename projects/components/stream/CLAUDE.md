# Claude Code Guide: STREAM Subsystem

**Version:** 1.0
**Last Updated:** 2025-10-17
**Purpose:** AI-specific guidance for working with STREAM subsystem

---

## Quick Context

**What:** STREAM - Scatter-gather Transfer Rapid Engine for AXI Memory
**Status:** 🟡 Initial design - tutorial-focused DMA engine
**Your Role:** Help users build a beginner-friendly descriptor-based DMA engine

**📖 Complete Specification:** `projects/components/stream/PRD.md` ← **Always reference this for technical details**

---

## 📖 Global Requirements Reference

**IMPORTANT: Review `/GLOBAL_REQUIREMENTS.md` for all mandatory requirements**

All mandatory requirements are consolidated in the global requirements document:
- **See:** `/GLOBAL_REQUIREMENTS.md` - Repository-wide mandatory requirements
- **STREAM-Specific:** Attribution format, tutorial focus (intentional simplifications)
- **Universal:** TB location, three methods, TBBase inheritance, 100% success

This CLAUDE.md provides STREAM-specific guidance. Also review:
- Root `/CLAUDE.md` - Repository-wide patterns
- `projects/components/CLAUDE.md` - Project area standards (reset macros, FPGA attributes)
- `bin/CocoTBFramework/CLAUDE.md` - Framework usage patterns

---

## Critical Rules for This Subsystem

### Rule #0: Attribution Format for Git Commits

**IMPORTANT:** When creating git commit messages for STREAM documentation or code:

**Use:**
```
Documentation and implementation support by Claude.
```

**Do NOT use:**
```
Co-Authored-By: Claude <noreply@anthropic.com>
```

**Rationale:** STREAM receives AI assistance for structure and clarity, while design concepts and architectural decisions remain human-authored.

### Rule #0.1: TUTORIAL FOCUS - Intentional Simplifications

**⚠️ STREAM is INTENTIONALLY SIMPLIFIED for educational purposes ⚠️**

**Key Simplifications (DO NOT "fix" these):**
1. **✅ Aligned addresses only** - No alignment fixup logic (kept for RAPIDS)
2. **✅ Length in beats** - Not bytes or chunks (simplifies math)
3. **✅ No circular buffers** - Explicit chain termination only
4. **✅ No credit management** - Simple transaction limits
5. **✅ Pure memory-to-memory** - No network interfaces

**When users ask "Can we add alignment fixup?":**
- ✅ **Correct answer:** "STREAM intentionally keeps addresses aligned for tutorial simplicity. For complex alignment, see RAPIDS."
- ❌ **Wrong answer:** "Sure, let me add alignment logic..." (defeats tutorial purpose!)

### Rule #0.1: Testbench Location and Test Structure (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 2.1 for complete requirement

**STREAM-Specific Directory Structure:**

```
projects/components/stream/dv/
├── tbclasses/                    # ★ STREAM TB classes (project area!)
│   ├── scheduler_tb.py           # Scheduler testbench
│   ├── descriptor_engine_tb.py   # Descriptor engine testbench
│   └── axi_engine_tb.py          # AXI engine testbenches
└── tests/fub_tests/              # Test runners import from tbclasses/
```

**STREAM Import Pattern:**
```python
# Import STREAM TB from project area
from projects.components.stream.dv.tbclasses.scheduler_tb import StreamSchedulerTB

# Shared utilities from framework
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
```

**📖 Complete Pattern:** `projects/components/rapids/CLAUDE.md` Rule #0.1

### Rule #0.2: Three Mandatory TB Methods (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 2.2 for complete requirement

**STREAM-Specific Context:**

STREAM has simpler config requirements than RAPIDS - most config can be set after reset.

**Standard STREAM Pattern:**
```python
class StreamSchedulerTB(TBBase):
    async def setup_clocks_and_reset(self):
        """Standard STREAM initialization"""
        await self.start_clock('clk', freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1
```

**Note:** Unlike RAPIDS, STREAM typically doesn't need config set before reset.

### Rule #1: REUSE from RAPIDS Where Appropriate

**Direct Reuse (No Modification):**
- ✅ `descriptor_engine.sv` - Works with STREAM descriptors
- ✅ `simple_sram.sv` - Standard dual-port SRAM
- ✅ Descriptor engine tests - Adapt imports only

**Adapt from RAPIDS:**
- ⚠️ `scheduler.sv` - **Simplify FSM** (no credit management, no control engines)
- ⚠️ AXI engines - **Create simplified versions** (no alignment fixup)

**Create New for STREAM:**
- 📝 APB config interface - PeakRDL-generated (like HPET), 8 channels, kick-off registers
- 📝 Top-level integration - Different interface set

**Always Ask Yourself:** "Can I reuse from RAPIDS instead of creating new?"

### Rule #2: Descriptor Format is DIFFERENT from RAPIDS

**STREAM Descriptor (256-bit):**
- `src_addr` (64-bit), `dst_addr` (64-bit), `length` (**beats**), `next_descriptor_ptr` (32-bit)
- **Length is in BEATS, not chunks!**

**RAPIDS Descriptor:**
- Uses chunks (4-byte units)
- Has alignment metadata

**When comparing/referencing RAPIDS:**
- ✅ "RAPIDS uses chunks, STREAM uses beats for tutorial simplicity"
- ❌ Don't assume RAPIDS descriptor format applies to STREAM

### Rule #3: Know the Shared Resources

**All 8 channels share:**
1. Descriptor fetch AXI master
2. Data read AXI master
3. Data write AXI master
4. SRAM buffer
5. MonBus reporter

**Arbitration is required!**
- Never assume exclusive access
- All shared resources need arbiter logic
- Priority-based round-robin (descriptor priority field)

---

## Architecture Quick Reference

### Block Organization

```
STREAM Architecture (Estimated: 8-10 modules)
├── APB Config
│   └── apb_config_slave.sv        (To be created)
│
├── Scheduler Group
│   ├── descriptor_engine.sv       (FROM RAPIDS - adapt imports)
│   ├── scheduler.sv               (Simplified from RAPIDS)
│   └── channel_arbiter.sv         (To be created)
│
├── Data Path
│   ├── axi_read_engine_v1.sv     (Version 1: Basic)
│   ├── axi_read_engine_v2.sv     (Version 2: Pipelined)
│   ├── axi_write_engine_v1.sv    (Version 1: Basic)
│   ├── axi_write_engine_v2.sv    (Version 2: Pipelined)
│   └── simple_sram.sv             (FROM RAPIDS - no changes)
│
└── MonBus Reporter
    └── monbus_reporter.sv         (To be created)
```

### Module Status

| Module | Source | Status | Notes |
|--------|--------|--------|-------|
| `descriptor_engine.sv` | RAPIDS (copy) | ✅ Copied | Adapt `#include` only |
| `simple_sram.sv` | RAPIDS (copy) | ✅ Copied | No changes needed |
| `stream_pkg.sv` | New | ✅ Created | Descriptor format defined |
| `stream_imports.svh` | New | ✅ Created | Package imports |
| `scheduler.sv` | RAPIDS (simplify) | ⏳ Pending | Remove credit mgmt, control engines |
| `apb_config_slave.sv` | New | ⏳ Pending | 8 channel registers |
| `axi_read_engine_v1.sv` | New | ⏳ Pending | Basic version |
| `axi_write_engine_v1.sv` | New | ⏳ Pending | Basic version |
| `channel_arbiter.sv` | New | ⏳ Pending | Priority-based round-robin |
| `monbus_reporter.sv` | New | ⏳ Pending | STREAM event codes |
| `stream_top.sv` | New | ⏳ Pending | Top-level integration |

---

## Common User Questions and Responses

### Q: "How is STREAM different from RAPIDS?"

**A: STREAM is intentionally simplified for tutorial purposes:**

**Simplifications:**
| Feature | RAPIDS | STREAM |
|---------|--------|--------|
| **Interfaces** | APB + AXI + Network | APB + AXI only |
| **Address Alignment** | Complex fixup | Aligned only |
| **Credit Management** | Exponential encoding | Simple limits |
| **Descriptor Length** | Chunks (4-byte) | Beats (data width) |
| **Control Engines** | Control read/write | None (direct APB) |

**Learning Path:**
1. **STREAM** - Basic DMA with scatter-gather
2. **STREAM Extended** - Add alignment fixup
3. **RAPIDS** - Full complexity with network + credit management

**📖 See:** `PRD.md` Section 2.1 for complete comparison table

### Q: "How do I kick off a transfer?"

**A: Single APB write starts descriptor chain:**

```systemverilog
// Software writes descriptor address to channel register
write_apb(ADDR_CH0_CTRL, 0x1000_0000);  // Start address of descriptor

// STREAM automatically:
// 1. Fetches descriptor from 0x1000_0000
// 2. Parses src_addr, dst_addr, length
// 3. Reads source data → SRAM
// 4. Writes SRAM → destination
// 5. Checks next_descriptor_ptr
//    - If != 0: Fetch next descriptor, repeat
//    - If == 0 or last flag set: Complete
```

**Chained Descriptors:**
```
Descriptor 0 @ 0x1000_0000:
  src_addr = 0x2000_0000
  dst_addr = 0x3000_0000
  length = 64 beats
  next_descriptor_ptr = 0x1000_0100  ← Points to next descriptor

Descriptor 1 @ 0x1000_0100:
  src_addr = 0x2000_1000
  dst_addr = 0x3000_1000
  length = 32 beats
  next_descriptor_ptr = 0x0000_0000  ← Last descriptor (0 = stop)
```

**📖 See:** `PRD.md` Section 3.2 for complete data flow

### Q: "How many channels can I use?"

**A: Maximum 8 independent channels:**

**Channel Operation:**
- Each channel has own FSM state
- Each channel can have separate descriptor chain
- All channels share: AXI masters, SRAM, MonBus

**Arbitration:**
- Priority-based (descriptor priority field)
- Round-robin within same priority
- Prevents starvation with timeout

**Example:**
```systemverilog
// Kick off 3 channels concurrently
write_apb(ADDR_CH0_CTRL, desc0_addr);  // Channel 0: Priority 7
write_apb(ADDR_CH1_CTRL, desc1_addr);  // Channel 1: Priority 5
write_apb(ADDR_CH2_CTRL, desc2_addr);  // Channel 2: Priority 5

// Service order: CH0 → CH1 → CH2 → CH0 → CH1 → CH2 ...
```

**📖 See:** `PRD.md` Section 7 for arbitration details

### Q: "What's the descriptor format?"

**A: 256-bit descriptor (4 × 64-bit words):**

```systemverilog
typedef struct packed {
    logic [63:0]  reserved;              // [255:192] Reserved
    logic [7:0]   priority;              // [207:200] Priority
    logic [3:0]   channel_id;            // [199:196] Channel ID
    logic         error;                 // [195] Error flag
    logic         last;                  // [194] Last in chain
    logic         interrupt;             // [193] Generate interrupt
    logic         valid;                 // [192] Valid descriptor
    logic [31:0]  next_descriptor_ptr;   // [191:160] Next descriptor address
    logic [31:0]  length;                // [159:128] Length in BEATS ★
    logic [63:0]  dst_addr;              // [127:64] Destination address
    logic [63:0]  src_addr;              // [63:0] Source address
} descriptor_t;
```

**★ CRITICAL:** `length` is in **BEATS**, not bytes or chunks!

**Example:**
```
Data width = 512 bits = 64 bytes
Length = 16 beats
Total transfer = 16 × 64 = 1024 bytes
```

**📖 See:** `PRD.md` Section 4.2 for complete descriptor specification

### Q: "How do I run STREAM tests?"

**A: Multi-layered test approach (same as RAPIDS):**

```bash
# 1. FUB (Functional Unit Block) Tests - Individual blocks
pytest projects/components/stream/dv/tests/fub_tests/scheduler/ -v
pytest projects/components/stream/dv/tests/fub_tests/descriptor_engine/ -v
pytest projects/components/stream/dv/tests/fub_tests/ -v  # All FUB tests

# 2. Integration Tests - Multi-block scenarios
pytest projects/components/stream/dv/tests/integration_tests/ -v

# Run with waveforms for debugging
pytest projects/components/stream/dv/tests/fub_tests/scheduler/ --vcd=debug.vcd
gtkwave debug.vcd
```

**Test Organization:**
- **FUB tests:** Focus on individual block functionality
- **Integration tests:** Verify block-to-block interfaces and complete data flows

---

## Integration Patterns

### Pattern 1: Basic STREAM Instantiation

```systemverilog
stream_top #(
    .NUM_CHANNELS(8),
    .DATA_WIDTH(512),
    .ADDR_WIDTH(64),
    .SRAM_DEPTH(4096)
) u_stream (
    // Clock and Reset
    .aclk               (system_clk),
    .aresetn            (system_rst_n),

    // APB Configuration Interface
    .s_apb_paddr        (apb_paddr),
    .s_apb_psel         (apb_psel),
    .s_apb_penable      (apb_penable),
    .s_apb_pwrite       (apb_pwrite),
    .s_apb_pwdata       (apb_pwdata),
    .s_apb_pready       (apb_pready),
    .s_apb_prdata       (apb_prdata),
    .s_apb_pslverr      (apb_pslverr),

    // AXI Master - Descriptor Fetch (256-bit)
    .m_axi_desc_araddr  (desc_araddr),
    .m_axi_desc_arlen   (desc_arlen),
    .m_axi_desc_arsize  (desc_arsize),
    .m_axi_desc_arvalid (desc_arvalid),
    .m_axi_desc_arready (desc_arready),
    .m_axi_desc_rdata   (desc_rdata),
    .m_axi_desc_rresp   (desc_rresp),
    .m_axi_desc_rlast   (desc_rlast),
    .m_axi_desc_rvalid  (desc_rvalid),
    .m_axi_desc_rready  (desc_rready),

    // AXI Master - Data Read (parameterizable width)
    .m_axi_rd_araddr    (rd_araddr),
    // ... (full AXI4 AR + R channels)

    // AXI Master - Data Write (parameterizable width)
    .m_axi_wr_awaddr    (wr_awaddr),
    // ... (full AXI4 AW + W + B channels)

    // MonBus Output
    .monbus_pkt_valid   (stream_mon_valid),
    .monbus_pkt_ready   (stream_mon_ready),
    .monbus_pkt_data    (stream_mon_data)
);
```

### Pattern 2: Descriptor Creation (Software Model)

```c
// C/C++ software model for descriptor creation
typedef struct {
    uint64_t src_addr;           // Source address (must be aligned!)
    uint64_t dst_addr;           // Destination address (must be aligned!)
    uint32_t length;             // Transfer length in BEATS
    uint32_t next_descriptor_ptr; // Next descriptor address (0 = last)
    uint8_t  control;            // valid | interrupt | last | error | channel_id | priority
} stream_descriptor_t;

// Create descriptor chain
stream_descriptor_t desc[2];

// Descriptor 0
desc[0].src_addr = 0x80000000ULL;  // Aligned to 64B (512-bit data)
desc[0].dst_addr = 0x90000000ULL;
desc[0].length = 64;  // 64 beats × 64 bytes = 4KB transfer
desc[0].next_descriptor_ptr = (uint32_t)&desc[1];  // Chain to next
desc[0].control = 0x01;  // valid = 1

// Descriptor 1 (last)
desc[1].src_addr = 0x80001000ULL;
desc[1].dst_addr = 0x90001000ULL;
desc[1].length = 32;  // 32 beats × 64 bytes = 2KB transfer
desc[1].next_descriptor_ptr = 0;  // Last descriptor
desc[1].control = 0x45;  // valid | last | interrupt

// Kick off transfer
write_apb_reg(CH0_CTRL, (uint32_t)&desc[0]);
```

### Pattern 3: MonBus Integration

```systemverilog
// Always add downstream FIFO for MonBus
gaxi_fifo_sync #(
    .DATA_WIDTH(64),
    .DEPTH(256)
) u_stream_mon_fifo (
    .i_clk      (aclk),
    .i_rst_n    (aresetn),
    .i_data     (monbus_pkt_data),
    .i_valid    (monbus_pkt_valid),
    .o_ready    (monbus_pkt_ready),
    .o_data     (fifo_mon_data),
    .o_valid    (fifo_mon_valid),
    .i_ready    (consumer_ready)
);
```

---

## Anti-Patterns to Catch

### ❌ Anti-Pattern 1: Adding Alignment Fixup

```systemverilog
❌ WRONG:
"Let me add alignment fixup logic to handle unaligned addresses..."

✅ CORRECTED:
"STREAM intentionally requires aligned addresses for tutorial simplicity.
If you need unaligned transfers, that's a great learning exercise for
extending STREAM, or use RAPIDS which has full alignment support."
```

### ❌ Anti-Pattern 2: Using Length in Bytes

```systemverilog
❌ WRONG:
descriptor.length = 4096;  // Thinking this is 4096 bytes

✅ CORRECTED:
// Length is in BEATS, not bytes!
// For 512-bit data width (64 bytes per beat):
descriptor.length = 4096 / 64;  // = 64 beats for 4096 bytes
```

### ❌ Anti-Pattern 3: Circular Buffer Descriptors

```systemverilog
❌ WRONG:
// Descriptor chain that loops back
desc[9].next_descriptor_ptr = &desc[0];  // Circular!

✅ CORRECTED:
"STREAM does not support circular buffers (no stop condition).
Always terminate chains explicitly:
  desc[last].next_descriptor_ptr = 0;  // Stop
  desc[last].last = 1;  // Explicit last flag
```

### ❌ Anti-Pattern 4: Assuming Exclusive Channel Access

```systemverilog
❌ WRONG:
// Assume channel has exclusive AXI master access
assign m_axi_arvalid = channel_request;  // No arbitration!

✅ CORRECTED:
// All channels share AXI masters - arbitration required
channel_arbiter u_arbiter (
    .ch_requests (channel_requests[7:0]),
    .ch_grant    (channel_grant[7:0]),
    .axi_master_available (axi_master_idle)
);
```

---

## Debugging Workflow

### Issue: Descriptor Not Fetched

**Check in order:**
1. ✅ APB write to CHx_CTRL register successful?
2. ✅ Descriptor address valid?
3. ✅ AXI descriptor master not stalled?
4. ✅ Descriptor memory accessible?
5. ✅ Arbiter granting descriptor fetch?

**Debug commands:**
```bash
pytest projects/components/stream/dv/tests/fub_tests/scheduler/ -v -s  # Verbose test
pytest projects/components/stream/dv/tests/fub_tests/scheduler/ --vcd=debug.vcd
gtkwave debug.vcd  # Inspect FSM state transitions
```

### Issue: Data Transfer Stalls

**Check in order:**
1. ✅ SRAM buffer depth sufficient?
2. ✅ Source/destination addresses aligned?
3. ✅ AXI read/write engines getting grants?
4. ✅ Downstream AXI ready signals asserted?
5. ✅ Channel not in error state?

**Waveform Analysis:**
- Check SRAM read/write pointers
- Verify AXI AR/AW/R/W/B handshakes
- Inspect scheduler FSM state
- Check arbiter grant signals

### Issue: Chained Descriptors Not Following

**Check in order:**
1. ✅ `next_descriptor_ptr` != 0?
2. ✅ `last` flag not set prematurely?
3. ✅ Descriptor fetch completing successfully?
4. ✅ Scheduler transitioning to CHAIN_CHECK state?
5. ✅ MonBus showing CHAIN_FETCH event?

---

## Testing Guidance

### Test Organization

```
projects/components/stream/dv/tests/
├── fub_tests/                  # Individual block tests
│   ├── descriptor_engine/      # Adapt from RAPIDS tests
│   ├── scheduler/              # Simplified scheduler tests
│   ├── axi_engines/            # Read/write engine tests
│   └── sram/                   # SRAM tests (from RAPIDS)
│
└── integration_tests/          # Multi-block scenarios
    ├── single_channel/         # Single channel transfers
    ├── multi_channel/          # 8-channel concurrent
    ├── chained_descriptors/    # Descriptor chain tests
    └── error_handling/         # Error recovery tests
```

### Test Levels

**Basic (Quick Smoke Tests):**
- Single descriptor, single channel
- Aligned addresses, simple transfers
- ~30 seconds runtime

**Medium (Typical Scenarios):**
- Multiple descriptors, 2-4 channels
- Chained descriptors (2-3 deep)
- ~90 seconds runtime

**Full (Comprehensive Validation):**
- All 8 channels concurrent
- Long descriptor chains (10+ deep)
- Error injection, stress testing
- ~180 seconds runtime

---

## Key Documentation Links

### Always Reference These

**This Subsystem:**
- `projects/components/stream/PRD.md` - **Complete specification**
- `projects/components/stream/README.md` - Quick start guide (to be created)
- `projects/components/stream/known_issues/` - Bug tracking

**Related:**
- `projects/components/rapids/PRD.md` - Parent architecture (for comparison)
- `rtl/amba/PRD.md` - MonBus integration
- `/PRD.md` - Master requirements
- `/CLAUDE.md` - Repository guide

---

## Quick Commands

```bash
# View complete specification
cat projects/components/stream/PRD.md

# Check package definition
cat projects/components/stream/rtl/includes/stream_pkg.sv

# Run tests (once created)
pytest projects/components/stream/dv/tests/fub_tests/ -v
pytest projects/components/stream/dv/tests/integration_tests/ -v

# Lint (once RTL created)
verilator --lint-only projects/components/stream/rtl/stream_fub/scheduler.sv

# Search for modules
find projects/components/stream/rtl/ -name "*.sv" -exec grep -H "^module" {} \;
```

---

## Remember

1. 📖 **Tutorial focus** - Intentional simplifications for learning
2. 🔄 **Reuse from RAPIDS** - Descriptor engine, SRAM, patterns
3. 📏 **Length in beats** - Not bytes or chunks!
4. 🔗 **Aligned addresses** - No fixup logic
5. ⛓️ **Chained descriptors** - No circular buffers
6. 🎯 **8 channels** - Shared resources, arbitration required
7. 🔍 **MonBus standard** - Same format as AMBA/RAPIDS
8. 🏗️ **Testbench reuse** - Always create TB classes in `bin/CocoTBFramework/tbclasses/stream/`

---

## PDF Generation Location

**IMPORTANT: PDF files should be generated in the docs directory:**
```
/mnt/data/github/rtldesignsherpa/projects/components/stream/docs/
```

**Quick Command:** Use the provided shell script:
```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/stream/docs
./generate_pdf.sh
```

The shell script will automatically:
1. Use the md_to_docx.py tool from bin/
2. Process the stream_spec index file
3. Generate both DOCX and PDF files in the docs/ directory
4. Create table of contents and title page

**📖 See:** `bin/md_to_docx.py` for complete implementation details

---

**Version:** 1.0
**Last Updated:** 2025-10-17
**Maintained By:** RTL Design Sherpa Project
