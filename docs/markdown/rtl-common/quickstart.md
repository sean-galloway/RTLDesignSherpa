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

# rtl-common Quick Start Guide

**Version:** 1.0
**Last Updated:** 2025-09-30
**Status:** Stable, Production-Ready

---

## Overview

The Common RTL Library is **49 reusable building blocks** for FPGA and ASIC designs. Every module is technology-agnostic, fully parameterizable, and verified with comprehensive CocoTB test suites.

**Quick Stats:**
- **49 modules** across 10 categories (arithmetic split out to `rtl/math/`, clock-crossing to `rtl/cdc/`)
- 🔧 **Technology agnostic** (FPGA/ASIC portable)
- 📖 **Well documented** (inline + external docs)
- 🧪 **Every module has a CocoTB test** under `val/common/`

---

## Module Categories

Counts live in one place — the [count table in index.md](index.md#module-count-by-category).
Here's the browse-oriented view of what's in each category:

| Category | Examples |
|----------|----------|
| Clock/Reset/CDC | clock_divider, clock_gate_ctrl, clock_pulse, glitch_free_n_dff_arn |
| Counters | counter, counter_bin, counter_bin_load, counter_freq_invariant, counter_load_clear, counter_ring |
| Data Integrity | dataint_crc, dataint_ecc_hamming, dataint_parity, dataint_checksum |
| Conversion & Encoding | bin_to_bcd, decoder, encoder, encoder_priority_enable, hex_to_7seg |
| Bit Ops & Search | count_leading_zeros, find_first_set, find_last_set, leading_one_trailing_one |
| Shifters & LFSRs | shifter_barrel, shifter_lfsr, shifter_lfsr_fibonacci, shifter_lfsr_galois |
| Arbiters | arbiter_round_robin, arbiter_round_robin_weighted, arbiter_priority_encoder |
| FIFOs | fifo_sync, fifo_control  (`fifo_async` moved to `rtl/cdc/`) |
| CAM | cam_tag |
| Miscellaneous | pwm, sort, bin_to_bcd, reverse_vector, mod_3_compress |

Arithmetic (`math_*`) split out into [`rtl/math/`](../rtl-math/index.md); its
docs are the [rtl-math](../rtl-math/index.md) book.

**Full per-module docs:** [docs/markdown/rtl-common/](index.md)

---

## Quick Start

### 1. Browse Available Modules

```bash
# List all modules
ls rtl/common/*.sv

# List by category
ls rtl/common/counter*.sv
ls rtl/common/arbiter*.sv
ls rtl/common/dataint*.sv

# Search for functionality
find rtl/common/ -name "*.sv" | xargs grep "fifo\|counter\|arbiter"
```

### 2. Check Module Interface

```bash
# View module header and parameters
head -50 rtl/common/counter_bin.sv

# Extract module definition
grep "^module\|parameter\|input\|output" rtl/common/counter_bin.sv
```

### 3. Review Test Examples

```bash
# Check if test exists
ls val/common/test_counter_bin.py

# View test for usage examples
cat val/common/test_counter_bin.py
```

### 4. Integrate into Your Design

```systemverilog
// Example: Instantiate binary counter
counter_bin #(
    .WIDTH(16),
    .MAX_VALUE(1000)
) u_my_counter (
    .i_clk      (my_clk),
    .i_rst_n    (my_rst_n),
    .i_enable   (count_enable),
    .o_count    (count_value),
    .o_overflow (count_ovf)
);
```

---

## Common Use Cases

### Use Case 1: Simple Event Counter

**Need:** Count events up to a maximum value

**Module:** `counter_bin.sv`

```systemverilog
counter_bin #(
    .WIDTH(8),
    .MAX_VALUE(255)
) u_event_counter (
    .i_clk      (clk),
    .i_rst_n    (rst_n),
    .i_enable   (event_detected),
    .o_count    (event_count),
    .o_overflow (max_events_reached)
);
```

---

### Use Case 2: Timeout Timer

**Need:** Detect when an operation takes too long

**Module:** `counter_freq_invariant.sv`

```systemverilog
counter_freq_invariant #(
    .CLK_FREQ_MHZ(100),      // 100 MHz clock
    .TIMEOUT_MS(50),         // 50 ms timeout
    .WIDTH(32)
) u_timeout (
    .i_clk      (clk),
    .i_rst_n    (rst_n),
    .i_enable   (operation_active),
    .o_count    (timer_count),
    .o_timeout  (timeout_occurred)
);
```

---

### Use Case 3: Multi-Master Arbitration

**Need:** Fair arbitration between 4 bus masters

**Module:** `arbiter_round_robin.sv`

```systemverilog
arbiter_round_robin #(
    .N(4),              // 4 requesters
    .REG_OUTPUT(1)      // Pipelined for timing
) u_bus_arbiter (
    .i_clk      (clk),
    .i_rst_n    (rst_n),
    .i_request  (master_requests[3:0]),  // One bit per master
    .o_grant    (master_grants[3:0]),    // One-hot grant
    .o_valid    (grant_valid)
);
```

---

### Use Case 4: CRC-32 (Ethernet)

**Need:** Calculate Ethernet CRC-32 for packet data

**Module:** `dataint_crc.sv`

```systemverilog
dataint_crc #(
    .POLYNOMIAL(32'h04C11DB7),   // CRC-32 Ethernet polynomial
    .WIDTH(32),
    .INIT_VALUE(32'hFFFFFFFF),
    .FINAL_XOR(32'hFFFFFFFF)
) u_crc32 (
    .i_clk      (clk),
    .i_rst_n    (rst_n),
    .i_data     (packet_data),
    .i_valid    (data_valid),
    .o_crc      (crc_result),
    .o_valid    (crc_valid)
);

// 250 CRC standards are exercised by the test suite via parameter configuration
```

---

### Use Case 5: Memory ECC (Single Error Correction)

**Need:** Protect memory with error correction

**Modules:** `dataint_ecc_hamming_encode_secded.sv` + `dataint_ecc_hamming_decode_secded.sv`

```systemverilog
// Encoder (write path) -- purely combinational
dataint_ecc_hamming_encode_secded #(
    .WIDTH(64)            // parameter is WIDTH, not DATA_WIDTH
) u_ecc_encoder (
    .data         (mem_write_data),
    .encoded_data (mem_data_with_ecc)   // one codeword: data + parity + SECDED bit
);

// Decoder (read path) -- CLOCKED, unlike the encoder
dataint_ecc_hamming_decode_secded #(
    .WIDTH(64)
) u_ecc_decoder (
    .clk                   (clk),
    .rst_n                 (rst_n),
    .enable                (1'b1),
    .hamming_data          (mem_read_data_with_ecc),
    .data                  (corrected_data),
    .error_detected        (single_bit_error),   // Correctable
    .double_error_detected (double_bit_error)    // Detectable only
);
```

---

### Use Case 6: Clock Domain Crossing (CDC)

**Need:** Safely cross a signal from one clock domain to another

**Module:** `cdc_synchronizer.sv` in `rtl/cdc/` (for data) or `sync_pulse.sv`
in `rtl/common/` (for pulses). There is no `sync_2ff` module — earlier revisions
of this guide named one, but it has never existed in the tree.

```systemverilog
// Option 1: Synchronize multi-bit data (rtl/cdc/cdc_synchronizer.sv)
// NOTE: a plain multi-flop synchronizer is only safe for signals whose bits
// can be sampled independently -- a single-bit flag, or a quasi-static value
// held stable across the crossing. For a multi-bit value that changes as a
// unit, use Gray coding (counter_bingray) or a handshake/async FIFO instead.
cdc_synchronizer #(
    .WIDTH(8),
    .FLOP_COUNT(3)
) u_data_sync (
    .clk        (dst_clk),
    .rst_n      (dst_rst_n),
    .async_in   (src_data),     // From source clock domain
    .sync_out   (dst_data)      // In destination clock domain
);

// Option 2: Synchronize single pulse
sync_pulse u_pulse_sync (
    .i_src_clk  (src_clk),
    .i_src_rst_n(src_rst_n),
    .i_pulse    (src_pulse),    // Single-cycle pulse
    .i_dst_clk  (dst_clk),
    .i_dst_rst_n(dst_rst_n),
    .o_pulse    (dst_pulse)     // Single-cycle pulse in dst domain
);
```

---

## Module Selection Guide

### "I need a counter..."

| Requirement | Module | Notes |
|-------------|--------|-------|
| Simple up counter | `counter_bin.sv` | Most common choice |
| With load/clear | `counter_load_clear.sv` | Explicit control |
| Time-based timeout | `counter_freq_invariant.sv` | Frequency-independent |
| Gray code | `counter_bingray.sv` (in `rtl/cdc/`) | For CDC |
| Ring counter | `counter_ring.sv` | Circular/sequential |
| Johnson counter | `counter_johnson.sv` (in `rtl/cdc/`) | 2N states with N FFs |

### "I need an arbiter..."

| Requirement | Module | Notes |
|-------------|--------|-------|
| Fair round-robin | `arbiter_round_robin.sv` | Most versatile |
| Weighted QoS | `arbiter_round_robin_weighted.sv` | Assign priorities |
| Fixed priority | `arbiter_priority_encoder.sv` | Lowest index wins |
| Minimal logic | `arbiter_round_robin_simple.sv` | Smallest area |

### "I need CRC..."

| Standard | Module | Configuration |
|----------|--------|---------------|
| Any CRC standard | `dataint_crc.sv` | Set POLYNOMIAL parameter |
| CRC-32 (Ethernet) | `dataint_crc.sv` | POLYNOMIAL=32'h04C11DB7 |
| CRC-16-CCITT | `dataint_crc.sv` | POLYNOMIAL=16'h1021 |
| CRC-8 | `dataint_crc.sv` | POLYNOMIAL=8'h07 |
| Custom | `dataint_crc_xor_shift.sv` | Build custom |

**📄 The validated CRC configurations (250 standards) are the `crc_parameters` table in `bin/TBClasses/common/crc_testing.py`, which drives `val/common/test_dataint_crc.py`.**

### "I need a FIFO..."

**For production designs:**
→ Use `rtl/amba/gaxi/gaxi_fifo_sync.sv` (solid, well-tested)

**For learning/simple cases:**
→ Check `rtl/common/` for basic FIFO examples

---

## Integration Checklist

When you integrate one of these modules into your design:

- [ ] **Search first** - Verify no better alternative exists
- [ ] **Read module header** - Understand parameters and constraints
- [ ] **Check parameter ranges** - Ensure your values are valid
- [ ] **Review test** - See `val/common/test_{module}.py` for examples
- [ ] **Match reset convention** - Use `i_rst_n` (active-low async)
- [ ] **Verify port widths** - Match parameter-dependent widths
- [ ] **Lint your design** - Run `verilator --lint-only` on top level
- [ ] **Test integration** - Create simple testbench
- [ ] **Check timing** - Verify no timing violations

---

## Testing Your Integration

### Option 1: Quick Functional Test

```bash
# Run existing module test to verify baseline
pytest val/common/test_{module}.py -v

# Example:
pytest val/common/test_counter_bin.py -v
```

### Option 2: Create Your Own Test

```python
# val/your_subsystem/test_your_design.py
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge

@cocotb.test()
async def test_your_design(dut):
    """Test your design that uses common modules"""

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1

    # Your test logic here
    # ...
```

### Option 3: Waveform Debug

```bash
# Run test with VCD waveform dump
pytest val/common/test_counter_bin.py -v --vcd=waves.vcd

# View waveforms
gtkwave waves.vcd

# Or use saved waveform config
gtkwave val/common/GTKW/counter_bin.gtkw
```

---

## Common Pitfalls and How to Avoid Them

These four show up in design reviews again and again. All of them are cheap to avoid once you know what to look for.

### ❌ Pitfall 1: Wrong Reset Polarity

**Wrong:**
```systemverilog
counter_bin u_counter (
    .i_rst_n(my_positive_reset),  // ERROR: Inverted!
    // ...
);
```

**Right:**
```systemverilog
counter_bin u_counter (
    .i_rst_n(~my_positive_reset),  // Invert if you have positive reset
    // OR better: use active-low reset throughout design
    .i_rst_n(my_rst_n),
    // ...
);
```

### ❌ Pitfall 2: Parameter Mismatch

**Wrong:**
```systemverilog
counter_bin #(
    .WIDTH(16)
    // Forgot MAX_VALUE - uses default 2^16-1
) u_counter (
    .o_count(count[7:0])  // ERROR: Width mismatch!
);
```

**Right:**
```systemverilog
counter_bin #(
    .WIDTH(8),          // Match output width
    .MAX_VALUE(200)
) u_counter (
    .o_count(count[7:0])  // Correct width
);
```

### ❌ Pitfall 3: Clock Domain Crossing Without Sync

**Wrong:**
```systemverilog
// Signal crosses from clk_a to clk_b domain
always_ff @(posedge clk_b)
    r_data <= signal_from_clk_a;  // ERROR: Metastability!
```

**Right:**
```systemverilog
// Use proper synchronizer (rtl/cdc/cdc_synchronizer.sv)
cdc_synchronizer #(.WIDTH(8), .FLOP_COUNT(3)) u_sync (
    .clk      (clk_b),
    .rst_n    (rst_n_b),
    .async_in (signal_from_clk_a),
    .sync_out (signal_in_clk_b)
);
```

### ❌ Pitfall 4: Creating New Module Without Searching

**Wrong:**
```systemverilog
// "I need a counter, let me write one..."
module my_new_counter (...);
  // Reinventing the wheel
endmodule
```

**Right:**
```bash
# "I need a counter, does one exist?"
ls rtl/common/counter*.sv
# → Found counter_bin.sv, counter_load_clear.sv, ...
# → Use existing module!
```

---

## Performance Considerations

### Area Optimization

**Small area:**
- Use `arbiter_round_robin_simple.sv` instead of full `arbiter_round_robin.sv`
- Minimize WIDTH parameters
- Use FFs instead of RAMs for small storage (<16 entries)

**Large area (more features):**
- Use full-featured modules
- Enable pipelining (REG_OUTPUT=1) for timing
- Use RAM-based FIFOs for large buffers

### Timing Optimization

**Critical path reduction:**
- Enable output pipelining where available
- Break long combinational chains
- Use registered versions of modules

**Example:**
```systemverilog
arbiter_round_robin #(
    .N(16),
    .REG_OUTPUT(1)  // Add output register for timing
) u_arbiter (
    // ...
);
```

### Power Optimization

**Clock gating:**
- Use `clock_gate_ctrl.sv` to gate inactive blocks
- Gate counter enables when not counting

**Example:**
```systemverilog
clock_gate_ctrl u_gate (
    .i_clk      (clk),
    .i_enable   (block_active),
    .o_clk_gated(clk_gated)
);

// Use clk_gated for power-sensitive logic
```

---

## Getting Help

### Documentation

- **This file** - Quick start and common use cases
- `docs/markdown/rtl-common/index.md` - Detailed specifications and module catalog
- `rtl/common/CLAUDE.md` - AI assistance guide for this subsystem
- `/CLAUDE.md` - Repository-wide guidance
- `/PRD.md` - Master project requirements

### Examples

- **Tests:** `val/common/test_*.py` - Working examples for every module
- **Usage:** Search rtl/amba/ and projects/components/ for integration examples

### Commands

```bash
# Find usage examples of a module
grep -r "counter_bin" rtl/amba/ projects/components/

# See how tests use the module
cat val/common/test_counter_bin.py

# Check module parameters
grep "parameter" rtl/common/counter_bin.sv
```

### For Claude Code Users

See `rtl/common/CLAUDE.md` for AI-specific guidance including:
- Module search strategies
- Common integration patterns
- Debugging tips
- Anti-patterns to avoid

---

## Quick Command Reference

```bash
# List all common modules
ls rtl/common/*.sv

# Search for specific functionality
find rtl/common/ -name "*.sv" | xargs grep -i "keyword"

# Run test for a module
pytest val/common/test_{module}.py -v

# Run all common tests
pytest val/common/ -v

# Lint a module
verilator --lint-only rtl/common/{module}.sv

# View waveforms
gtkwave waves.vcd

# Count lines of code
wc -l rtl/common/*.sv

# Find instantiations of a module
grep -r "module_name" rtl/
```

---

## What's Next?

### Explore Other Subsystems

- **`rtl/amba/`** - AMBA protocol infrastructure (AXI, APB, AXIS monitors)
- **`projects/components/dmas/rapids/`** - Rapid AXI Programmable In-band Descriptor System (example accelerator)
- **`bin/TBClasses/`** - Verification infrastructure

### Create Your Own Modules

1. Follow the patterns in the existing modules
2. Use consistent naming (`category_function.sv`)
3. Add comprehensive header comments
4. Create a test in `val/common/`
5. Update this README if you're adding a new category

### Contribute

- Report issues
- Suggest improvements
- Share integration examples
- Document lessons learned

---

**Questions?** Check `docs/markdown/rtl-common/index.md` for detailed specifications or `rtl/common/CLAUDE.md` for AI assistance guidance.

**Version:** 1.0
**Last Updated:** 2025-09-30
**Maintained By:** RTL Design Sherpa Project
