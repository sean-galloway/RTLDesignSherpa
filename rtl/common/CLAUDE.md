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

# Claude Code Guide: Common RTL Library

**Version:** 1.0
**Last Updated:** 2025-09-30
**Purpose:** AI-specific guidance for working with rtl/common/ subsystem

---

## Quick Context

**What:** Reusable technology-agnostic building blocks (counters, arbiters, CRC, CDC, etc.); math primitives now live in `rtl/math/`
**Status:** Stable, mature baseline - production ready
**Your Role:** Help users integrate existing modules, rarely create new ones

---

## Global Requirements Reference

**IMPORTANT: Review `/GLOBAL_REQUIREMENTS.md` for mandatory RTL standards**

All mandatory requirements are consolidated in the global requirements document:
- **See:** `/GLOBAL_REQUIREMENTS.md` - Repository-wide mandatory requirements
- **RTL Focus:** Reset convention, array syntax, search-before-create
- **Reset:** active-low throughout, but the port is `rst_n`, not `i_rst_n` (see Rule #3)

This CLAUDE.md provides common RTL library guidance. Also review:
- Root `/CLAUDE.md` - Repository-wide patterns
- `projects/components/CLAUDE.md` - Project area standards (if creating new components)

---

## Critical Rules for This Subsystem

### Rule #0: Verification Architecture (MANDATORY)

**See:** `/GLOBAL_REQUIREMENTS.md` Sections 2.1, 2.3, 2.4 for complete requirements

**Common RTL Three-Layer Pattern:**
1. **TB:** `bin/TBClasses/common/{module}_tb.py`
2. **Scoreboard:** `bin/TBClasses/scoreboards/common/{module}_scoreboard.py`
3. **Test:** `val/common/test_{module}.py`

**Common RTL typically uses queue access** - counters, arbiters, and similar blocks are simple control paths.

**Complete Guide:** `docs/user-guides/VERIFICATION_ARCHITECTURE_GUIDE.md`

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

WRONG Response:
"Let me create a counter module for you..."

RIGHT Response:
"Let me check existing counters first:
[searches rtl/common/counter*.sv]
Found counter_bin.sv - it wraps at MAX, with the MSB as a wrap flag:
counter_bin #(.WIDTH(8), .MAX(100)) u_cnt (.clk, .rst_n, .enable,
                                           .counter_bin_curr, .counter_bin_next);
```

### Rule #2: Verify Modules in Context

Always check how existing designs use a module:

```bash
# See usage examples
grep -r "counter_bin\|arbiter_round_robin" rtl/amba/ projects/components/

# Check test for API
cat val/common/test_counter_bin.py
```

### Rule #3: Reset Convention (MANDATORY)

**See:** `/GLOBAL_REQUIREMENTS.md` Section 1.1 for complete requirement

**Common RTL Status:** Active-low everywhere, but the port is named **`rst_n`**,
not `i_rst_n`. Measured across `rtl/common/*.sv`: 28 modules expose `rst_n`, one
exposes `aresetn` (`clock_gate_ctrl`), and **none** expose `i_rst_n`; the other
20 have no reset port at all (`icg` among them). Write `.rst_n(...)` — an `i_rst_n` connection will not elaborate against
these modules. The polarity requirement in `/GLOBAL_REQUIREMENTS.md` §1.1 is met; the
`i_`-prefix naming is not, and reconciling the two is an open decision, not
something to patch per-instantiation.

---

## Module Quick Reference for AI

### When User Says: "I need..."

| User Request | First Check | Likely Solution |
|---|---|---|
| "...a counter" | `ls rtl/common/counter*.sv` | `counter_bin.sv` (most cases) |
| "...a timer/timeout" | `counter_freq_invariant.sv` | 1 us `tick`; build the timeout on it |
| "...an arbiter" | `ls rtl/common/arbiter*.sv` | `arbiter_round_robin.sv` |
| "...CRC calculation" | `dataint_crc.sv` | 250 validated configurations |
| "...error correction" | `dataint_ecc_hamming_*.sv` | SECDED ECC |
| "...parity" | `dataint_parity.sv` | Even/odd parity |
| "...clock divider" | `clock_divider.sv` | But warn: prefer PLL |
| "...synchronizer/CDC" | `glitch_free_n_dff_arn.sv` or `sync_pulse.sv` | Safe CDC |
| "...FIFO" | Point to `rtl/amba/gaxi/` | Production FIFOs |
| "...priority encoder" | `arbiter_priority_encoder.sv` | Exists |
| "...leading zeros" | `count_leading_zeros.sv` | Exists (scans MSB down) |
| "...trailing zeros / alignment" | `count_trailing_zeros.sv` | Exists (scans LSB up) - do NOT bit-reverse into CLZ |
| "...Gray code" | `bin2gray.sv`, `gray2bin.sv` | Both directions |

### Counter Selection Matrix

| Requirement | Module | Parameters |
|---|---|---|
| FIFO pointer / wrap counting | `counter_bin.sv` | WIDTH, MAX |
| With load/clear | `counter_load_clear.sv` | WIDTH |
| Microsecond time base | `counter_freq_invariant.sv` | COUNTER_WIDTH, MIN/MAX_FREQ_MHZ |
| Ring/circular | `counter_ring.sv` | WIDTH |
| Plain up-counter | `counter.sv` | WIDTH |
| FIFO pointer with load | `counter_bin_load.sv` | WIDTH, MAX |

`counter_bingray.sv` and `counter_johnson.sv` are **not** in `rtl/common/` --
they moved to `rtl/cdc/`. `ls rtl/common/counter*.sv` returns the six above.

### Arbiter Selection Matrix

| Requirement | Module | Notes |
|---|---|---|
| Fair arbitration | `arbiter_round_robin.sv` | Most versatile, pipelinable |
| Weighted QoS | `arbiter_round_robin_weighted.sv` | Assign weights |
| Fixed priority | `arbiter_priority_encoder.sv` | Lowest index wins |
| Minimal area | `arbiter_round_robin_simple.sv` | Simplified version |

---

## Common Integration Patterns

### Pattern 1: Basic Counter Instantiation

```systemverilog
counter_bin #(
    .WIDTH(5),            // Total width: MSB is the wrap flag, WIDTH-1 count bits
    .MAX  (10)            // Count bits run 0..MAX-1, then the MSB toggles
) u_counter_instance_name (
    .clk              (clock_signal),
    .rst_n            (reset_n_signal),
    .enable           (count_enable_signal),
    .counter_bin_curr (count_output),
    .counter_bin_next (count_next_output)
);
```

**This is a FIFO-pointer counter, not a plain event counter.** The lower
`WIDTH-1` bits count `0..MAX-1`; on wrap they clear and the MSB **toggles**, so
that a matching read/write pointer pair distinguishes full from empty. There is
no overflow output — the MSB flip is the wrap signal, and `counter_bin_next`
exposes the pre-registered value for the same-cycle comparisons FIFO control
needs.

**When to suggest:**
- FIFO / ring-buffer read and write pointers
- Any wrap-at-MAX counter where full-vs-empty must be distinguishable
- For plain event counting with a load or clear, prefer `counter_load_clear.sv`

### Pattern 2: Timeout Timer

```systemverilog
counter_freq_invariant #(
    .COUNTER_WIDTH   (16),   // Width of the microsecond counter
    .MIN_FREQ_MHZ    (5),    // Lowest supported clock
    .MAX_FREQ_MHZ    (220),  // Highest supported clock
    .NUM_FREQ_ENTRIES(16)    // Prescaler LUT entries
) u_us_tick (
    .clk          (clk),
    .rst_n        (rst_n),
    .sync_reset_n (sync_clear_n),   // Synchronous restart, separate from rst_n
    .freq_sel     (freq_sel),       // Selects the prescaler LUT entry
    .o_counter    (microseconds),   // Free-running microsecond count
    .tick         (us_tick)         // One-cycle pulse per microsecond
);
```

**This is a microsecond time base, not a timeout timer.** It divides whatever
clock it is given down to a 1 us `tick` using a prescaler chosen at runtime by
`freq_sel`, so the same RTL keeps real-time meaning across clock frequencies —
that is what "frequency invariant" means here. It has no timeout parameter and
no timeout output.

**When to suggest:**
- A time base that must stay correct when the clock frequency changes
- Feeding a timeout counter you build on top of `tick` — set your own threshold
  and compare against `o_counter`
- For a self-contained timeout, count `tick` pulses in a `counter_load_clear.sv`

### Pattern 3: Multi-Master Arbitration

```systemverilog
arbiter_round_robin #(
    .CLIENTS     (4),   // Number of requesters
    .WAIT_GNT_ACK(0)    // 1 = hold the grant until grant_ack; 0 = single cycle
) u_arbiter (
    .clk        (clk),
    .rst_n      (rst_n),
    .block_arb  (1'b0),             // Hold arbitration off while high
    .request    (req_vec[3:0]),     // One bit per requester
    .grant_ack  ('0),               // Only meaningful when WAIT_GNT_ACK=1
    .grant_valid(grant_valid),
    .grant      (grant_vec[3:0]),   // One-hot grant
    .grant_id   (grant_idx),        // $clog2(CLIENTS) bits
    .last_grant (last_grant_vec)
);
```

**When to suggest:**
- Multiple masters accessing shared resource
- Bus arbitration (memory, register file, FIFO)
- Task scheduling

### Pattern 4: CRC Calculation

```systemverilog
dataint_crc #(
    .DATA_WIDTH(32),             // Must be CHUNKS x 8
    .CRC_WIDTH (32),
    .REFIN     (1),              // Reflect input bytes
    .REFOUT    (1)               // Reflect the output
) u_crc (
    .POLY             (32'h04C11DB7),   // CRC-32 Ethernet -- a PORT, not a param
    .POLY_INIT        (32'hFFFFFFFF),
    .XOROUT           (32'hFFFFFFFF),
    .clk              (clk),
    .rst_n            (rst_n),
    .load_crc_start   (crc_restart),    // Reload POLY_INIT
    .load_from_cascade(data_valid),     // Absorb `data` this cycle
    .cascade_sel      (4'b1000),        // One-hot: how many of the 4 bytes are live
    .data             (data_word),
    .crc              (crc_result)
);
```

**The configuration is wired, not parameterized.** `POLY`, `POLY_INIT` and
`XOROUT` are input ports, so a design can retune the CRC at run time; only the
widths and the reflect flags are parameters. `cascade_sel` is one-hot over
`CHUNKS = DATA_WIDTH/8` and selects how many bytes of `data` participate, which
is what makes trailing partial words work. There is no output-valid — `crc` is
the running value.

**When to suggest:**
- User needs CRC for communication protocol
- Data integrity checking
- Packet validation

**Common CRC Standards** (drive these onto `POLY`):
- CRC-32 (Ethernet): `POLY=32'h04C11DB7`
- CRC-16-CCITT: `POLY=16'h1021`
- CRC-8: `POLY=8'h07`

The 250 validated configurations are the `crc_parameters` table in
`bin/TBClasses/common/crc_testing.py`, which drives `val/common/test_dataint_crc.py`.

### Pattern 5: Clock Domain Crossing (CDC)

```systemverilog
// For multi-bit data (slow changing)
glitch_free_n_dff_arn #(
    .FLOP_COUNT(3),
    .WIDTH(8)
) u_sync_data (
    .clk   (dst_clk),
    .rst_n (dst_rst_n),
    .d     (src_data),   // From source clock domain
    .q     (sync_data)   // Synchronized to dst_clk
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

**Warning:** always emphasize proper CDC. This is critical for correctness.

---

## Anti-Patterns to Catch and Correct

### Anti-Pattern 1: Creating New Counter

```
User: "Create a module that counts from 0 to N"

WRONG:
"Here's a new counter module:
module my_counter #(parameter MAX=100) ..."

RIGHT:
"Use existing counter_bin.sv:
counter_bin #(.WIDTH($clog2(N+1)+1), .MAX(N)) u_cnt (...);"
```

### Anti-Pattern 2: Wrong Reset Polarity

```systemverilog
WRONG (User's code):
always_ff @(posedge clk or posedge rst) begin
    if (rst) r_state <= 0;

CORRECTED:
"This design uses active-low reset. Change to:
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) r_state <= 0;
"
```

### Anti-Pattern 3: Unsafe CDC

```systemverilog
WRONG (User's code):
always_ff @(posedge clk_b)
    r_data <= signal_from_clk_a;  // METASTABILITY!

CORRECTED:
"This crosses clock domains unsafely. Use synchronizer:
glitch_free_n_dff_arn #(.FLOP_COUNT(3), .WIDTH(WIDTH)) u_sync (
    .clk(clk_b), .rst_n(rst_b_n), .d(signal_from_clk_a), .q(r_data)
);
"
```

### Anti-Pattern 4: Parameter Width Mismatch

```systemverilog
WRONG (User's code):
counter_bin #(.WIDTH(16)) u_cnt (
    .counter_bin_curr(count[7:0])  // WIDTH mismatch!
);

CORRECTED:
"Counter WIDTH parameter (16) doesn't match output width (8). Fix:
counter_bin #(.WIDTH(8)) u_cnt (
    .counter_bin_curr(count[7:0])
);
"
```

### Anti-Pattern 5: Reinventing Clock Divider

```
User: "I need to divide my 100MHz clock by 2"

WRONG:
"Create a clock divider with a toggle FF..."

RIGHT:
"Use clock_divider.sv, BUT better: use PLL/clock manager if available.
Clock dividers create derived clocks which can cause timing issues.

If you must use divider:
clock_divider #(.N(1), .COUNTER_WIDTH(64), .PO_WIDTH(8)) u_div (...);
The divisors are runtime inputs (pick-off selects), not a DIV_RATIO parameter."
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
grep -r "module_name" rtl/amba/ projects/components/
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
    .WIDTH(9),          // 8 count bits + wrap flag
    .MAX  (200)
) u_event_counter (
    .clk              (clk),
    .rst_n            (rst_n),
    .enable           (event_valid),
    .counter_bin_curr (event_count),
    .counter_bin_next (event_count_next)
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
|---|---|
| counter.sv | Plain up-counter |
| counter_load_clear.sv | Count to a runtime match value, with load/clear |
| counter_bin.sv | FIFO/ring pointer -- wraps at MAX, MSB toggles |
| counter_bin_load.sv | FIFO pointer plus load and variable increment |
| counter_freq_invariant.sv | Microsecond `tick` time base |
| counter_ring.sv | Circular/sequential (WIDTH >= 2) |

`counter_bingray.sv` and `counter_johnson.sv` are in `rtl/cdc/`, not here.

"For plain counting to a value, use **counter_load_clear.sv**; counter_bin.sv is
a FIFO-pointer counter whose MSB is a wrap flag, not a count bit."

### Q: "How do I calculate CRC-32?"

**A:** Direct answer with code:
```systemverilog
dataint_crc #(
    .DATA_WIDTH(32),
    .CRC_WIDTH (32),
    .REFIN     (1),
    .REFOUT    (1)
) u_crc32 (
    .POLY     (32'h04C11DB7),   // CRC-32 Ethernet -- a PORT, not a parameter
    .POLY_INIT(32'hFFFFFFFF),
    .XOROUT   (32'hFFFFFFFF),
    .clk, .rst_n, .load_crc_start, .load_from_cascade,
    .cascade_sel, .data, .crc
);
```

"The configuration is wired, not parameterized: POLY/POLY_INIT/XOROUT are input
ports, so the CRC can be retuned at run time. 250 configurations are validated
in crc_testing.py."

### Q: "I need a FIFO"

**A:** Redirect to better location:
"For production FIFOs, use **rtl/amba/gaxi/gaxi_fifo_sync.sv** (more robust).

rtl/common/ has basic FIFO examples for learning, but gaxi FIFOs are better tested."

### Q: "How do I safely cross clock domains?"

**A:** Emphasize safety first:
```systemverilog
// For data (quasi-static):
glitch_free_n_dff_arn #(.FLOP_COUNT(3), .WIDTH(8)) u_sync (
    .clk(dst_clk), .rst_n(dst_rst_n), .d(src_data), .q(dst_data)
);

// For pulses:
sync_pulse u_sync_pulse (
    .i_src_clk(src_clk), .i_pulse(src_pulse),
    .i_dst_clk(dst_clk), .o_pulse(dst_pulse)
);
```

"**Critical:** never cross clock domains without proper synchronization."

### Q: "Can I create a new module in rtl/common/?"

**A:** Set clear expectations:
"**Only if:**
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
//   - WIDTH: Total width; MSB is the wrap flag, WIDTH-1 count bits (default: 5)
//   - MAX: Count bits run 0..MAX-1, then clear and toggle the MSB (default: 10)
// Ports:
//   - clk: Clock input
//   - rst_n: Active-low asynchronous reset
//   - enable: Count enable (active-high)
//   - counter_bin_curr: Registered count [WIDTH-1:0]
//   - counter_bin_next: Combinational next count [WIDTH-1:0]
// Notes:
//   - FIFO-pointer semantics: the MSB toggle is what separates full from empty
//   - There is no overflow output; compare the MSBs of a pointer pair instead
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
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    await RisingEdge(dut.clk)

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
- **Not** `REG_OUTPUT` on the arbiters — no arbiter in `rtl/common` declares
  such a parameter (`arbiter_round_robin` takes `CLIENTS`/`WAIT_GNT_ACK`/`N`,
  `arbiter_round_robin_weighted` adds `MAX_LEVELS`), and their grant outputs
  are already registered in an `always_ff`. There is nothing to enable.
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
grep -r "module_name" rtl/amba/ projects/components/

# View test
cat val/common/test_module.py

# Run test
pytest val/common/test_module.py -v

# Lint
verilator --lint-only rtl/common/module.sv
```

---

## Key Files for Reference

- **docs/markdown/rtl-common/index.md** - Detailed module specifications
- **docs/markdown/rtl-common/quickstart.md** - Quick start guide (docs/markdown/rtl-common/index.md links here)
- **val/common/test_*.py** - Test examples
- **/CLAUDE.md** - Repository-wide AI guidance
- **/PRD.md** - Master project requirements

---

## Remember

1. **Search first** - dozens of modules already exist (plus `rtl/math/` for arithmetic)
2. **Verify in tests** - Check val/common/test_*.py for API
3. **Reuse patterns** - Look at rtl/amba/ and projects/components/ usage
4. **Document decisions** - Why existing modules don't fit
5. **Safety critical** - CDC, reset polarity, parameter widths

---

**Version:** 1.0
**Last Updated:** 2025-09-30
**Maintained By:** RTL Design Sherpa Project
