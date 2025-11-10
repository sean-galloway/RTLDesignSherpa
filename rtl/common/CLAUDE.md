# Claude Code Guide: Common RTL Library

**Version:** 1.0
**Last Updated:** 2025-09-30
**Purpose:** AI-specific guidance for working with rtl/common/ subsystem

---

## Quick Context

**What:** 86 reusable technology-agnostic building blocks (counters, arbiters, math, CRC, etc.)
**Status:** ✅ Stable, mature baseline - production ready
**Your Role:** Help users integrate existing modules, rarely create new ones

---

## 📖 Global Requirements Reference

**IMPORTANT: Review `/GLOBAL_REQUIREMENTS.md` for mandatory RTL standards**

All mandatory requirements are consolidated in the global requirements document:
- **See:** `/GLOBAL_REQUIREMENTS.md` - Repository-wide mandatory requirements
- **RTL Focus:** Reset convention, array syntax, search-before-create
- **Already Compliant:** rtl/common/ already uses proper reset patterns

This CLAUDE.md provides common RTL library guidance. Also review:
- Root `/CLAUDE.md` - Repository-wide patterns
- `projects/components/CLAUDE.md` - Project area standards (if creating new components)

---

## Critical Rules for This Subsystem

### Rule #0: Verification Architecture (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Sections 2.1, 2.3, 2.4 for complete requirements

**Common RTL Three-Layer Pattern:**
1. **TB:** `bin/CocoTBFramework/tbclasses/common/{module}_tb.py`
2. **Scoreboard:** `bin/CocoTBFramework/scoreboards/common/{module}_scoreboard.py`
3. **Test:** `val/common/test_{module}.py`

**Common RTL typically uses queue access** - counters, arbiters, and math blocks are simple control paths.

**📖 Complete Guide:** `docs/VERIFICATION_ARCHITECTURE_GUIDE.md`

---

### Rule #1: ALWAYS Search First, Create Last

**Before suggesting ANY new module:**

```bash
# REQUIRED: Search existing modules
ls rtl/common/{category}*.sv

# Example searches:
ls rtl/common/counter*.sv    # Find counters
ls rtl/common/arbiter*.sv    # Find arbiters
ls rtl/common/dataint*.sv    # Find CRC/ECC/parity
```

**Decision Tree:**
1. **Exact match exists** → Use it, done
2. **Close match exists** → Adapt with parameters
3. **No match found** → Document search, propose new
4. **Didn't search** → STOP, go back and search

**Example Dialog:**
```
User: "I need a counter that counts up to 100"

❌ WRONG Response:
"Let me create a counter module for you..."

✅ RIGHT Response:
"Let me check existing counters first:
[searches rtl/common/counter*.sv]
Found counter_bin.sv which supports configurable MAX_VALUE!
Here's how to use it:
counter_bin #(.WIDTH(7), .MAX_VALUE(100)) u_cnt (...);
```

### Rule #2: Verify Modules in Context

Always check how existing designs use a module:

```bash
# See usage examples
grep -r "counter_bin\|arbiter_round_robin" rtl/amba/ rtl/rapids/

# Check test for API
cat val/common/test_counter_bin.py
```

### Rule #3: Reset Convention (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 1.1 for complete requirement

**Common RTL Status:** ✅ Already compliant - all modules use `i_rst_n` or `aresetn` (active-low)

---

## Module Quick Reference for AI

### When User Says: "I need..."

| User Request | First Check | Likely Solution |
|--------------|-------------|-----------------|
| "...a counter" | `ls rtl/common/counter*.sv` | `counter_bin.sv` (most cases) |
| "...a timer/timeout" | `counter_freq_invariant.sv` | Time-based counter |
| "...an arbiter" | `ls rtl/common/arbiter*.sv` | `arbiter_round_robin.sv` |
| "...CRC calculation" | `dataint_crc.sv` | Supports ~300 standards |
| "...error correction" | `dataint_ecc_hamming_*.sv` | SECDED ECC |
| "...parity" | `dataint_parity.sv` | Even/odd parity |
| "...clock divider" | `clock_divider.sv` | But warn: prefer PLL |
| "...synchronizer/CDC" | `sync_2ff.sv` or `sync_pulse.sv` | Safe CDC |
| "...FIFO" | Point to `rtl/amba/gaxi/` | Production FIFOs |
| "...priority encoder" | `priority_encoder.sv` | Exists |
| "...leading zeros" | `count_leading_zeros.sv` | Exists |
| "...Gray code" | `bin2gray.sv`, `gray2bin.sv` | Both directions |

### Counter Selection Matrix

| Requirement | Module | Parameters |
|-------------|--------|------------|
| Basic counting | `counter_bin.sv` | WIDTH, MAX_VALUE |
| With load/clear | `counter_load_clear.sv` | WIDTH |
| Time-based | `counter_freq_invariant.sv` | CLK_FREQ_MHZ, TIMEOUT_MS |
| Gray code | `counter_bingray.sv` | WIDTH |
| Ring/circular | `counter_ring.sv` | WIDTH |
| Johnson | `counter_johnson.sv` | WIDTH |

### Arbiter Selection Matrix

| Requirement | Module | Notes |
|-------------|--------|-------|
| Fair arbitration | `arbiter_round_robin.sv` | Most versatile, pipelinable |
| Weighted QoS | `arbiter_round_robin_weighted.sv` | Assign weights |
| Fixed priority | `arbiter_priority_encoder.sv` | Lowest index wins |
| Minimal area | `arbiter_round_robin_simple.sv` | Simplified version |

---

## Common Integration Patterns

### Pattern 1: Basic Counter Instantiation

```systemverilog
counter_bin #(
    .WIDTH(16),           // Bit width
    .MAX_VALUE(1000)      // Max count before overflow
) u_counter_instance_name (
    .i_clk      (clock_signal),
    .i_rst_n    (reset_n_signal),
    .i_enable   (count_enable_signal),
    .o_count    (count_output),
    .o_overflow (overflow_flag)
);
```

**When to suggest:**
- User needs event counting
- State machine iteration counting
- Frame/packet counting

### Pattern 2: Timeout Timer

```systemverilog
counter_freq_invariant #(
    .CLK_FREQ_MHZ(100),   // Match actual clock frequency
    .TIMEOUT_MS(50),      // Desired timeout in milliseconds
    .WIDTH(32)            // Usually 32-bit for time
) u_timeout_timer (
    .i_clk      (clk),
    .i_rst_n    (rst_n),
    .i_enable   (operation_active),
    .o_count    (timer_value),
    .o_timeout  (timeout_detected)
);
```

**When to suggest:**
- User needs timeout detection
- Protocol watchdog timers
- Handshake timeout monitors

### Pattern 3: Multi-Master Arbitration

```systemverilog
arbiter_round_robin #(
    .N(4),              // Number of requesters
    .REG_OUTPUT(1)      // 1=pipelined for timing, 0=combinational
) u_arbiter (
    .i_clk      (clk),
    .i_rst_n    (rst_n),
    .i_request  (req_vec[3:0]),    // One bit per requester
    .o_grant    (grant_vec[3:0]),  // One-hot grant output
    .o_valid    (grant_valid)
);
```

**When to suggest:**
- Multiple masters accessing shared resource
- Bus arbitration (memory, register file, FIFO)
- Task scheduling

### Pattern 4: CRC Calculation

```systemverilog
dataint_crc #(
    .POLYNOMIAL(32'h04C11DB7),   // CRC-32 Ethernet
    .WIDTH(32),
    .INIT_VALUE(32'hFFFFFFFF),   // Standard CRC-32
    .FINAL_XOR(32'hFFFFFFFF)     // Standard CRC-32
) u_crc (
    .i_clk      (clk),
    .i_rst_n    (rst_n),
    .i_data     (data_byte),
    .i_valid    (data_valid),
    .o_crc      (crc_result),
    .o_valid    (crc_valid)
);
```

**When to suggest:**
- User needs CRC for communication protocol
- Data integrity checking
- Packet validation

**Common CRC Standards:**
- CRC-32 (Ethernet): `POLYNOMIAL=32'h04C11DB7`
- CRC-16-CCITT: `POLYNOMIAL=16'h1021`
- CRC-8: `POLYNOMIAL=8'h07`

### Pattern 5: Clock Domain Crossing (CDC)

```systemverilog
// For multi-bit data (slow changing)
sync_2ff #(
    .WIDTH(8)
) u_sync_data (
    .i_clk   (dst_clk),
    .i_rst_n (dst_rst_n),
    .i_data  (src_data),     // From source clock domain
    .o_data  (sync_data)     // Synchronized to dst_clk
);

// For single-cycle pulses
sync_pulse u_sync_pulse (
    .i_src_clk   (src_clk),
    .i_src_rst_n (src_rst_n),
    .i_pulse     (src_pulse),   // Single-cycle pulse
    .i_dst_clk   (dst_clk),
    .i_dst_rst_n (dst_rst_n),
    .o_pulse     (dst_pulse)    // Single-cycle in dst domain
);
```

**When to suggest:**
- User crossing clock domains
- Async signals entering design
- Multi-clock system integration

**⚠️ WARNING:** Always emphasize proper CDC! This is critical for correctness.

---

## Anti-Patterns to Catch and Correct

### ❌ Anti-Pattern 1: Creating New Counter

```
User: "Create a module that counts from 0 to N"

❌ WRONG:
"Here's a new counter module:
module my_counter #(parameter MAX=100) ..."

✅ RIGHT:
"Use existing counter_bin.sv:
counter_bin #(.WIDTH($clog2(N+1)), .MAX_VALUE(N)) u_cnt (...);"
```

### ❌ Anti-Pattern 2: Wrong Reset Polarity

```systemverilog
❌ WRONG (User's code):
always_ff @(posedge clk or posedge rst) begin
    if (rst) r_state <= 0;

✅ CORRECTED:
"This design uses active-low reset. Change to:
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) r_state <= 0;
"
```

### ❌ Anti-Pattern 3: Unsafe CDC

```systemverilog
❌ WRONG (User's code):
always_ff @(posedge clk_b)
    r_data <= signal_from_clk_a;  // METASTABILITY!

✅ CORRECTED:
"This crosses clock domains unsafely. Use synchronizer:
sync_2ff #(.WIDTH(WIDTH)) u_sync (
    .i_clk(clk_b), .i_data(signal_from_clk_a), .o_data(r_data)
);
"
```

### ❌ Anti-Pattern 4: Parameter Width Mismatch

```systemverilog
❌ WRONG (User's code):
counter_bin #(.WIDTH(16)) u_cnt (
    .o_count(count[7:0])  // WIDTH mismatch!
);

✅ CORRECTED:
"Counter WIDTH parameter (16) doesn't match output width (8). Fix:
counter_bin #(.WIDTH(8)) u_cnt (
    .o_count(count[7:0])
);
"
```

### ❌ Anti-Pattern 5: Reinventing Clock Divider

```
User: "I need to divide my 100MHz clock by 2"

❌ WRONG:
"Create a clock divider with a toggle FF..."

✅ RIGHT:
"Use clock_divider.sv, BUT better: use PLL/clock manager if available.
Clock dividers create derived clocks which can cause timing issues.

If you must use divider:
clock_divider #(.DIV_RATIO(2)) u_div (...);"
```

---

## Workflow for Claude Code

### Step 1: Understand User Need

**Extract key requirements:**
- What functionality? (counting, arbitration, CRC, etc.)
- Any special constraints? (timing, area, power)
- Integration context? (clock domain, data width, etc.)

### Step 2: Search Existing Modules

**ALWAYS run these commands:**
```bash
# Search by category
ls rtl/common/{category}*.sv

# Search by keyword
find rtl/common/ -name "*.sv" | xargs grep -i "keyword"

# Check usage examples
grep -r "module_name" rtl/amba/ rtl/rapids/
```

**Document your search in response:**
"I searched rtl/common/ and found counter_bin.sv which matches your requirements..."

### Step 3: Verify Module Fits

**Check module interface:**
```bash
# View parameters and ports
grep "module\|parameter\|input\|output" rtl/common/module_name.sv | head -30
```

**Check test for usage:**
```bash
cat val/common/test_module_name.py
```

### Step 4: Provide Integration Code

**Include:**
1. Module instantiation with correct parameters
2. Signal connections
3. Any constraints or notes
4. Test command to verify

**Example:**
```systemverilog
// Instantiate counter
counter_bin #(
    .WIDTH(8),
    .MAX_VALUE(200)
) u_event_counter (
    .i_clk      (clk),
    .i_rst_n    (rst_n),
    .i_enable   (event_valid),
    .o_count    (event_count),
    .o_overflow (max_reached)
);

// Test: pytest val/common/test_counter_bin.py -v
```

### Step 5: Lint and Test Guidance

**Always suggest:**
```bash
# Lint top-level design
verilator --lint-only your_top_module.sv

# Run existing module test
pytest val/common/test_{module}.py -v
```

---

## Common User Questions and Answers

### Q: "What counters are available?"

**A:** Search and summarize:
```bash
ls rtl/common/counter*.sv
```

Then provide table:
| Module | Use Case |
|--------|----------|
| counter_bin.sv | General purpose, most common |
| counter_load_clear.sv | With load/clear control |
| counter_freq_invariant.sv | Time-based (ms/us) |
| counter_bingray.sv | Gray code for CDC |
| counter_ring.sv | Circular/sequential |
| counter_johnson.sv | 2N states with N FFs |

"For basic counting to a max value, use **counter_bin.sv**"

### Q: "How do I calculate CRC-32?"

**A:** Direct answer with code:
```systemverilog
dataint_crc #(
    .POLYNOMIAL(32'h04C11DB7),  // CRC-32 Ethernet
    .WIDTH(32),
    .INIT_VALUE(32'hFFFFFFFF),
    .FINAL_XOR(32'hFFFFFFFF)
) u_crc32 (...);
```

"The dataint_crc module supports ~300 CRC standards via parameters."

### Q: "I need a FIFO"

**A:** Redirect to better location:
"For production FIFOs, use **rtl/amba/gaxi/gaxi_fifo_sync.sv** (more robust).

rtl/common/ has basic FIFO examples for learning, but gaxi FIFOs are better tested."

### Q: "How do I safely cross clock domains?"

**A:** Emphasize safety first:
```systemverilog
// For data (quasi-static):
sync_2ff #(.WIDTH(8)) u_sync (
    .i_clk(dst_clk), .i_data(src_data), .o_data(dst_data)
);

// For pulses:
sync_pulse u_sync_pulse (
    .i_src_clk(src_clk), .i_pulse(src_pulse),
    .i_dst_clk(dst_clk), .o_pulse(dst_pulse)
);
```

"⚠️ **CRITICAL:** Never cross clock domains without proper synchronization!"

### Q: "Can I create a new module in rtl/common/?"

**A:** Set clear expectations:
"✅ **Only if:**
1. Searched thoroughly and no existing module works
2. Documented why existing modules insufficient
3. Follows naming convention: {category}_{function}.sv
4. Technology-agnostic (no vendor primitives)
5. Includes comprehensive header comment
6. Has test in val/common/

**Example justification:**
'Searched: counter_bin.sv, counter_load_clear.sv, counter_freq_invariant.sv
None support bidirectional counting with configurable step size.
Creating: counter_updown_step.sv'

Otherwise, adapt existing modules with parameters."

---

## Module Documentation Standards

### Every Module Must Have:

**1. Header Comment Block:**
```systemverilog
// Module: counter_bin
// Description: Binary up counter with configurable maximum value
// Parameters:
//   - WIDTH: Counter bit width (range: 1-64, default: 8)
//   - MAX_VALUE: Maximum count before overflow (range: 1 to 2^WIDTH-1, default: 2^WIDTH-1)
// Ports:
//   - i_clk: Clock input
//   - i_rst_n: Active-low asynchronous reset
//   - i_enable: Count enable (active-high)
//   - o_count: Current count value [WIDTH-1:0]
//   - o_overflow: Overflow flag (asserted when count == MAX_VALUE)
// Notes:
//   - Overflows and wraps to 0 when count reaches MAX_VALUE
//   - Can be used as modulo counter by setting MAX_VALUE
//   - Enable input gates counting operation
```

**2. Parameter Documentation:**
- Valid ranges
- Default values
- Units (if applicable)
- Constraints/dependencies

**3. Port Documentation:**
- Direction and purpose
- Width (especially parameterized)
- Active level (high/low)
- Special timing requirements

**4. Usage Notes:**
- Common use cases
- Gotchas or limitations
- Related modules
- Test file location

### When Suggesting New Modules

**Include all of the above** plus:
- Justification (why no existing module works)
- Comparison to alternatives
- Test plan

---

## Test Integration Guidance

### Running Existing Tests

```bash
# Test specific module
pytest val/common/test_counter_bin.py -v

# Test all counters
pytest val/common/test_counter*.py -v

# Test all common modules
pytest val/common/ -v

# With waveform dump
pytest val/common/test_counter_bin.py -v --vcd=waves.vcd
gtkwave waves.vcd
```

### Creating Tests for New Integrations

**Template:**
```python
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

@cocotb.test()
async def test_my_integration(dut):
    """Test description"""

    # Start clock
    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.i_rst_n.value = 0
    await RisingEdge(dut.i_clk)
    await RisingEdge(dut.i_clk)
    dut.i_rst_n.value = 1
    await RisingEdge(dut.i_clk)

    # Test logic
    # ...

    assert condition, "Error message"
```

---

## Performance and Optimization

### Area Optimization

**Suggest when user mentions area constraints:**
- Use smaller WIDTH parameters
- Choose simpler variants (e.g., `arbiter_round_robin_simple.sv`)
- Minimize buffer depths

### Timing Optimization

**Suggest when user has timing issues:**
- Enable pipelining: `REG_OUTPUT=1` on arbiters
- Break long combinational paths
- Check critical paths with static timing analysis

### Power Optimization

**Suggest when user mentions power:**
- Clock gating: `clock_gate_ctrl.sv`
- Gate enables when inactive
- Reduce toggle rates

---

## Quick Command Reference

```bash
# Search for modules
ls rtl/common/{category}*.sv
find rtl/common/ -name "*.sv" | xargs grep -i "keyword"

# Check module interface
grep "module\|parameter\|input\|output" rtl/common/module.sv

# Find usage examples
grep -r "module_name" rtl/amba/ rtl/rapids/

# View test
cat val/common/test_module.py

# Run test
pytest val/common/test_module.py -v

# Lint
verilator --lint-only rtl/common/module.sv
```

---

## Key Files for Reference

- **rtl/common/PRD.md** - Detailed module specifications
- **rtl/common/README.md** - Quick start guide
- **val/common/test_*.py** - Test examples
- **/CLAUDE.md** - Repository-wide AI guidance
- **/PRD.md** - Master project requirements

---

## Remember

1. 🔍 **Search first** - 86 modules already exist
2. ✅ **Verify in tests** - Check val/common/test_*.py for API
3. 🔄 **Reuse patterns** - Look at rtl/amba/ and rtl/rapids/ usage
4. 📝 **Document decisions** - Why existing modules don't fit
5. ⚠️ **Safety critical** - CDC, reset polarity, parameter widths

---

**Version:** 1.0
**Last Updated:** 2025-09-30
**Maintained By:** RTL Design Sherpa Project
