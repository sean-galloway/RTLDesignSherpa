# Common RTL Library - Quick Start Guide

**Version:** 1.0
**Last Updated:** 2025-09-30
**Status:** Stable, Production-Ready

---

## Overview

The Common RTL Library provides **86 reusable building blocks** for FPGA and ASIC designs. All modules are technology-agnostic, fully parameterizable, and verified with comprehensive CocoTB test suites.

**Quick Stats:**
- 📦 **86 modules** across 9 categories
- ✅ **~90% test coverage** (functional)
- 🔧 **Technology agnostic** (FPGA/ASIC portable)
- 📖 **Well documented** (inline + external docs)
- 🧪 **Fully verified** (CocoTB + pytest)

---

## Module Categories

| Category | Count | Examples |
|----------|-------|----------|
| **Counters** | 9 | Binary, Gray, Johnson, Ring, Frequency-invariant |
| **Arbiters** | 5 | Round-robin, Weighted, Priority |
| **Data Integrity** | 9 | CRC, ECC (Hamming SECDED), Parity, Checksum |
| **Math** | 6 | Leading zeros, Bin2Gray, Bin2BCD |
| **Clock Utilities** | 6 | Dividers, Gates, Pulse generators, Debounce |
| **Encoders/Decoders** | 5 | Binary, Priority, One-hot |
| **Synchronizers** | 4 | 2FF sync, Pulse sync, Handshake, CDC |
| **Memory/Storage** | 6 | CAM, FIFOs, Register file, Shift registers |
| **Miscellaneous** | 36+ | Muxes, Shifters, Width converters, and more |

**📄 Complete list:** See `rtl/common/PRD.md` for detailed module descriptions

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

**Need:** Detect when operation takes too long

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

// Supports ~300 CRC standards via parameter configuration!
```

---

### Use Case 5: Memory ECC (Single Error Correction)

**Need:** Protect memory with error correction

**Modules:** `dataint_ecc_hamming_encode_secded.sv` + `dataint_ecc_hamming_decode_secded.sv`

```systemverilog
// Encoder (write path)
dataint_ecc_hamming_encode_secded #(
    .DATA_WIDTH(64)       // 64-bit data
) u_ecc_encoder (
    .i_data      (mem_write_data),
    .o_encoded   (mem_data_with_ecc),    // Data + parity bits
    .o_parity    (ecc_parity_bits)
);

// Decoder (read path)
dataint_ecc_hamming_decode_secded #(
    .DATA_WIDTH(64)
) u_ecc_decoder (
    .i_encoded       (mem_read_data_with_ecc),
    .o_data          (corrected_data),
    .o_error_single  (single_bit_error),      // Correctable
    .o_error_double  (double_bit_error)       // Detectable only
);
```

---

### Use Case 6: Clock Domain Crossing (CDC)

**Need:** Safely cross signal from one clock domain to another

**Module:** `sync_2ff.sv` (for data) or `sync_pulse.sv` (for pulses)

```systemverilog
// Option 1: Synchronize multi-bit data
sync_2ff #(
    .WIDTH(8)
) u_data_sync (
    .i_clk      (dst_clk),
    .i_rst_n    (dst_rst_n),
    .i_data     (src_data),     // From source clock domain
    .o_data     (dst_data)      // In destination clock domain
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
| Gray code | `counter_bingray.sv` | For CDC |
| Ring counter | `counter_ring.sv` | Circular/sequential |
| Johnson counter | `counter_johnson.sv` | 2N states with N FFs |

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

**📄 See `rtl/common/PRD.md` for ~300 validated CRC polynomials**

### "I need a FIFO..."

**For production designs:**
→ Use `rtl/amba/gaxi/gaxi_fifo_sync.sv` (robust, well-tested)

**For learning/simple cases:**
→ Check `rtl/common/` for basic FIFO examples

---

## Integration Checklist

When integrating a common module into your design:

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
gtkwave val/common/GTKW/counter_bin_debug.gtkw
```

---

## Common Pitfalls and How to Avoid Them

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
// Use proper synchronizer
sync_2ff #(.WIDTH(8)) u_sync (
    .i_clk   (clk_b),
    .i_rst_n (rst_n_b),
    .i_data  (signal_from_clk_a),
    .o_data  (signal_in_clk_b)
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
- `rtl/common/PRD.md` - Detailed specifications and module catalog
- `rtl/common/CLAUDE.md` - AI assistance guide for this subsystem
- `/CLAUDE.md` - Repository-wide guidance
- `/PRD.md` - Master project requirements

### Examples

- **Tests:** `val/common/test_*.py` - Working examples for every module
- **Usage:** Search rtl/amba/ and rtl/rapids/ for integration examples

### Commands

```bash
# Find usage examples of a module
grep -r "counter_bin" rtl/amba/ rtl/rapids/

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
- **`rtl/rapids/`** - Rapid AXI Programmable In-band Descriptor System (example accelerator)
- **`bin/CocoTBFramework/`** - Verification infrastructure

### Create Your Own Modules

1. Follow patterns in existing modules
2. Use consistent naming (`category_function.sv`)
3. Add comprehensive header comments
4. Create test in `val/common/`
5. Update this README if adding new category

### Contribute

- Report issues
- Suggest improvements
- Share integration examples
- Document lessons learned

---

**Questions?** Check `rtl/common/PRD.md` for detailed specifications or `rtl/common/CLAUDE.md` for AI assistance guidance.

**Version:** 1.0
**Last Updated:** 2025-09-30
**Maintained By:** RTL Design Sherpa Project
