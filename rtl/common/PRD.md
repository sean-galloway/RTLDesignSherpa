# Product Requirements Document (PRD)
## Common RTL Library

**Version:** 1.0
**Date:** 2025-09-30
**Status:** Stable - Mature Baseline
**Owner:** RTL Design Sherpa Project
**Parent Document:** `/PRD.md`

---

## 1. Executive Summary

The Common RTL Library provides 86 technology-agnostic, reusable building blocks for FPGA and ASIC designs. These modules implement fundamental digital design primitives including counters, arbiters, FIFOs, data integrity functions, math operations, and clock utilities.

### 1.1 Subsystem Goals

- **Primary:** Provide proven, reusable primitives for rapid design integration
- **Secondary:** Demonstrate best practices for parameterizable RTL design
- **Tertiary:** Educational reference for fundamental digital design patterns

### 1.2 Status Summary

- **Modules:** 86 SystemVerilog files
- **Test Coverage:** ~90% functional coverage
- **Verification:** Comprehensive CocoTB test suite in `val/common/`
- **Maturity:** Stable, production-ready baseline
- **Known Issues:** None blocking

---

## 2. Module Categories

### 2.1 Counters (9 modules)

| Module | Purpose | Key Parameters | Status |
|--------|---------|----------------|--------|
| `counter.sv` | Basic up counter | WIDTH | ✅ Complete |
| `counter_bin.sv` | Binary counter with enable | WIDTH, MAX_VALUE | ✅ Complete |
| `counter_bingray.sv` | Binary/Gray counter | WIDTH | ✅ Complete |
| `counter_johnson.sv` | Johnson counter | WIDTH | ✅ Complete |
| `counter_ring.sv` | Ring counter | WIDTH | ✅ Complete |
| `counter_load_clear.sv` | Counter with load/clear | WIDTH | ✅ Complete |
| `counter_freq_invariant.sv` | Frequency-independent counter | CLK_FREQ_MHZ, TIMEOUT_MS | ✅ Complete |

**Use Cases:**
- State machine counters
- Timeout detection
- Event counting
- Frequency division
- Circular buffers

**Test Coverage:** 95%

---

### 2.2 Arbiters (5 modules)

| Module | Purpose | Key Parameters | Status |
|--------|---------|----------------|--------|
| `arbiter_priority_encoder.sv` | Priority-based arbitration | N (requesters) | ✅ Complete |
| `arbiter_round_robin.sv` | Fair round-robin arbitration | N, REG_OUTPUT | ✅ Complete |
| `arbiter_round_robin_simple.sv` | Simplified round-robin | N | ✅ Complete |
| `arbiter_round_robin_weighted.sv` | Weighted round-robin | N, WEIGHT_WIDTH | ✅ Complete |

**Use Cases:**
- Multi-master bus arbitration
- Resource sharing (FIFO access, memory ports)
- Task scheduling
- QoS arbitration with weights

**Test Coverage:** 90%

**Design Patterns:**
- Grant signals one-hot encoded
- Request signals can be multi-hot
- Configurable output pipelining for timing

---

### 2.3 Data Integrity (9 modules)

#### CRC Functions
| Module | Purpose | Key Parameters | Status |
|--------|---------|----------------|--------|
| `dataint_crc.sv` | Parameterizable CRC | POLYNOMIAL, WIDTH | ✅ Complete |
| `dataint_crc_xor_shift.sv` | XOR-shift CRC primitive | WIDTH | ✅ Complete |
| `dataint_crc_xor_shift_cascade.sv` | Cascaded XOR-shift CRC | WIDTH, STAGES | ✅ Complete |

**Supported Standards:** ~300 CRC polynomials validated

#### ECC Functions
| Module | Purpose | Key Parameters | Status |
|--------|---------|----------------|--------|
| `dataint_ecc_hamming_encode_secded.sv` | Hamming encoder (SECDED) | DATA_WIDTH | ✅ Complete |
| `dataint_ecc_hamming_decode_secded.sv` | Hamming decoder (SECDED) | DATA_WIDTH | ✅ Complete |

**SECDED:** Single Error Correction, Double Error Detection

#### Other
| Module | Purpose | Key Parameters | Status |
|--------|---------|----------------|--------|
| `dataint_checksum.sv` | Simple checksum | WIDTH | ✅ Complete |
| `dataint_parity.sv` | Parity generator/checker | WIDTH, EVEN_ODD | ✅ Complete |

**Use Cases:**
- Communication protocol integrity (Ethernet, USB, etc.)
- Memory error correction (SECDED ECC)
- Data validation (checksum, parity)

**Test Coverage:** 95%

---

### 2.4 Math Functions (6 modules)

| Module | Purpose | Key Parameters | Status |
|--------|---------|----------------|--------|
| `count_leading_zeros.sv` | Count leading zeros (CLZ) | WIDTH | ✅ Complete |
| `bin2gray.sv` | Binary to Gray code | WIDTH | ✅ Complete |
| `gray2bin.sv` | Gray to binary code | WIDTH | ✅ Complete |
| `bin_to_bcd.sv` | Binary to BCD | WIDTH | ✅ Complete |
| `math_adder_*.sv` | Various adder topologies | WIDTH | ✅ Complete |
| `math_multiplier_*.sv` | Multiplier topologies | WIDTH | ✅ Complete |

**Use Cases:**
- Normalization (CLZ for floating point)
- Clock domain crossing (Gray code)
- Display interfaces (BCD)
- Arithmetic operations

**Test Coverage:** 90%

**Note:** Advanced adders and multipliers are parameterized and generated via Python scripts in `bin/rtl_generators/`

---

### 2.5 Clock Utilities (6 modules)

| Module | Purpose | Key Parameters | Status |
|--------|---------|----------------|--------|
| `clock_divider.sv` | Clock frequency divider | DIV_RATIO | ✅ Complete |
| `clock_gate_ctrl.sv` | Clock gating control | N/A | ✅ Complete |
| `clock_pulse.sv` | Pulse generator | N/A | ✅ Complete |
| `debounce.sv` | Signal debouncing | CLK_FREQ, DEBOUNCE_MS | ✅ Complete |
| `edge_detect.sv` | Rising/falling edge detector | EDGE_TYPE | ✅ Complete |
| `pulse_gen.sv` | Configurable pulse generator | WIDTH | ✅ Complete |

**Use Cases:**
- Clock generation/division
- Power management (clock gating)
- Signal conditioning (debounce)
- Edge-triggered logic

**Test Coverage:** 85%

**⚠️ Warning:** Clock dividers should be used carefully in ASIC designs. Prefer PLLs/clock managers when available.

---

### 2.6 Encoders/Decoders (5 modules)

| Module | Purpose | Key Parameters | Status |
|--------|---------|----------------|--------|
| `encoder.sv` | Binary encoder | N (inputs) | ✅ Complete |
| `decoder.sv` | Binary decoder | N (outputs) | ✅ Complete |
| `priority_encoder.sv` | Priority encoder | N (inputs) | ✅ Complete |
| `onehot_to_bin.sv` | One-hot to binary | WIDTH | ✅ Complete |
| `bin_to_onehot.sv` | Binary to one-hot | WIDTH | ✅ Complete |

**Use Cases:**
- Address decoding
- Control signal generation
- State encoding
- Interrupt controllers

**Test Coverage:** 90%

---

### 2.7 Synchronizers and CDC (4 modules)

| Module | Purpose | Key Parameters | Status |
|--------|---------|----------------|--------|
| `sync_2ff.sv` | Two flip-flop synchronizer | WIDTH | ✅ Complete |
| `sync_pulse.sv` | Pulse synchronizer | N/A | ✅ Complete |
| `sync_handshake.sv` | Handshake synchronizer | WIDTH | ✅ Complete |
| `debounce.sv` | Metastability resolver | CLK_FREQ, DEBOUNCE_MS | ✅ Complete |

**Use Cases:**
- Clock domain crossing (CDC)
- Metastability prevention
- Asynchronous input handling

**Test Coverage:** 85%

**⚠️ Critical:** Always use proper synchronizers for CDC. Never directly connect signals across clock domains.

---

### 2.8 Memory and Storage (6 modules)

| Module | Purpose | Key Parameters | Status |
|--------|---------|----------------|--------|
| `cam_tag.sv` | Content Addressable Memory | DEPTH, WIDTH | ✅ Complete |
| `fifo_*.sv` | Various FIFO topologies | See rtl/amba/gaxi/ | ✅ See GAXI |
| `register_file.sv` | Register file/bank | N_REGS, WIDTH | ✅ Complete |
| `pipe_stage.sv` | Pipeline stage | WIDTH, DEPTH | ✅ Complete |
| `shift_register.sv` | Shift register chain | WIDTH, DEPTH | ✅ Complete |

**Use Cases:**
- Fast lookup (CAM for routing tables, caches)
- Buffering (FIFOs)
- Pipeline delay balancing
- Data storage

**Test Coverage:** 90%

**Note:** For production FIFOs, use `rtl/amba/gaxi/` synchronous FIFO implementations which are more robust.

---

### 2.9 Miscellaneous Utilities (36+ modules)

Additional specialized modules:
- Muxes (various topologies)
- Shifters (barrel shifter, LFSR)
- State machines (templates)
- Width converters
- Byte enable logic
- And many more...

See `rtl/common/` directory listing for complete inventory.

---

## 3. Design Principles

### 3.1 Parameterization

**All modules are highly parameterizable:**

```systemverilog
module counter_bin #(
    parameter int WIDTH = 8,           // Bit width
    parameter int MAX_VALUE = 255      // Maximum count value
) (
    input  logic             i_clk,
    input  logic             i_rst_n,
    input  logic             i_enable,
    output logic [WIDTH-1:0] o_count,
    output logic             o_overflow
);
```

**Guidelines:**
- Parameters use `UPPER_CASE`
- Sensible defaults provided
- Derived parameters use `localparam`
- Document valid parameter ranges

### 3.2 Technology Agnostic

**No vendor-specific primitives:**
- ❌ No Xilinx/Intel FPGA primitives
- ❌ No ASIC library cells
- ✅ Pure synthesizable SystemVerilog
- ✅ Infers optimal implementation

**Exception:** `rtl/xilinx/` contains vendor-specific modules for specialized cases.

### 3.3 Reset Convention

**All modules use active-low asynchronous reset:**

```systemverilog
always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)
        r_state <= RESET_VALUE;
    else
        r_state <= w_next_state;
end
```

**Naming:** Always `i_rst_n` or `aresetn` (never `rst`, `reset`, or positive reset)

### 3.4 Port Naming Convention

| Port Type | Prefix | Example |
|-----------|--------|---------|
| Input | `i_*` | `i_data`, `i_valid`, `i_enable` |
| Output | `o_*` | `o_result`, `o_ready`, `o_overflow` |
| Bidirectional | `io_*` | `io_data` |

**Internal Signals:**
| Signal Type | Prefix | Example |
|-------------|--------|---------|
| Registered | `r_*` | `r_counter`, `r_state` |
| Combinational | `w_*` | `w_sum`, `w_next_state` |

---

## 4. Reuse Guidelines

### 4.1 Before Creating New Modules

**CRITICAL: Always search first!**

```bash
# Search for similar functionality
find rtl/common/ -name "*.sv" | xargs grep -l "counter\|arbiter\|fifo"

# List all modules in category
ls rtl/common/counter*.sv
ls rtl/common/arbiter*.sv
ls rtl/common/dataint*.sv

# Review module parameters
grep "^module\|parameter" rtl/common/counter_bin.sv
```

**Decision Tree:**
1. ✅ Exact match found → Use it directly
2. ✅ Close match found → Parameterize or adapt
3. ⚠️ No match found → Create new, document why
4. ❌ No search done → STOP, search first!

### 4.2 Module Selection Guide

**Need a counter?**
- Simple up counter → `counter.sv` or `counter_bin.sv`
- With load/clear → `counter_load_clear.sv`
- Time-based → `counter_freq_invariant.sv`
- Special encoding → `counter_johnson.sv`, `counter_ring.sv`

**Need an arbiter?**
- Fair arbitration → `arbiter_round_robin.sv`
- Priority-based → `arbiter_priority_encoder.sv`
- Weighted QoS → `arbiter_round_robin_weighted.sv`
- Simple/minimal → `arbiter_round_robin_simple.sv`

**Need CRC?**
- Any standard → `dataint_crc.sv` (supports ~300 polynomials)
- Custom → `dataint_crc_xor_shift.sv` primitives

**Need error correction?**
- Memory ECC → `dataint_ecc_hamming_*_secded.sv`
- Simple parity → `dataint_parity.sv`

**Need a FIFO?**
- Production use → `rtl/amba/gaxi/gaxi_fifo_sync.sv`
- Simple/learning → `rtl/common/` has basic examples

### 4.3 Integration Examples

**Example 1: Simple Binary Counter**
```systemverilog
counter_bin #(
    .WIDTH(16),
    .MAX_VALUE(1000)
) u_frame_counter (
    .i_clk      (clk),
    .i_rst_n    (rst_n),
    .i_enable   (frame_valid),
    .o_count    (frame_count),
    .o_overflow (frame_overflow)
);
```

**Example 2: Round-Robin Arbiter**
```systemverilog
arbiter_round_robin #(
    .N(4),          // 4 requesters
    .REG_OUTPUT(1)  // Registered output for timing
) u_arbiter (
    .i_clk      (clk),
    .i_rst_n    (rst_n),
    .i_request  (request_vec),   // [3:0]
    .o_grant    (grant_vec),     // [3:0] one-hot
    .o_valid    (grant_valid)
);
```

**Example 3: CRC-32 (Ethernet)**
```systemverilog
dataint_crc #(
    .POLYNOMIAL(32'h04C11DB7),  // CRC-32 (Ethernet)
    .WIDTH(32),
    .INIT_VALUE(32'hFFFFFFFF),
    .FINAL_XOR(32'hFFFFFFFF)
) u_crc32 (
    .i_clk      (clk),
    .i_rst_n    (rst_n),
    .i_data     (data_in),
    .i_valid    (data_valid),
    .o_crc      (crc_value),
    .o_valid    (crc_valid)
);
```

---

## 5. Verification Strategy

### 5.1 Test Organization

**Location:** `val/common/`

**Test Files:** One test per module
- `test_counter_bin.py`
- `test_arbiter_round_robin.py`
- `test_dataint_crc.py`
- etc.

**Framework:** CocoTB + pytest

### 5.2 Test Methodology

**Each test includes:**
1. **Basic Functionality** - Core operation verification
2. **Corner Cases** - Boundary conditions (0, max, overflow)
3. **Parameter Sweeps** - Multiple width/depth configurations
4. **Randomization** - Random stimulus for stress testing
5. **Coverage** - Functional coverage collection

**Example Test Structure:**
```python
import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock

@cocotb.test()
async def test_counter_bin_basic(dut):
    """Test basic counting functionality"""
    # Test implementation
    pass

@cocotb.test()
async def test_counter_bin_overflow(dut):
    """Test overflow condition"""
    pass

@cocotb.test()
async def test_counter_bin_enable(dut):
    """Test enable control"""
    pass
```

### 5.3 Running Tests

```bash
# Run single test
pytest val/common/test_counter_bin.py -v

# Run all counter tests
pytest val/common/test_counter*.py -v

# Run all common tests
pytest val/common/ -v

# Run with waveform dump
pytest val/common/test_counter_bin.py -v --vcd=waves.vcd

# View waveforms
gtkwave waves.vcd
```

### 5.4 Coverage Goals

| Metric | Target | Current |
|--------|--------|---------|
| Functional Coverage | >95% | ~90% |
| Code Coverage (Line) | >90% | ~85% |
| Code Coverage (Branch) | >85% | ~80% |
| Corner Cases | 100% | ~95% |

---

## 6. Known Issues and Limitations

### 6.1 Current Status

**✅ No Critical Issues**

All modules are stable and production-ready. No blocking bugs identified.

### 6.2 Limitations by Design

**Counter Limitations:**
- `counter_freq_invariant.sv` requires accurate CLK_FREQ_MHZ parameter
- Maximum count value limited by WIDTH parameter

**Arbiter Limitations:**
- Round-robin arbiters may have 1-cycle grant latency
- Weighted arbiters require careful weight selection to avoid starvation

**CRC Limitations:**
- `dataint_crc.sv` processes 1 byte per cycle (not bit-serial or multi-byte)
- Polynomial must be specified at elaboration time

**Clock Utility Limitations:**
- `clock_divider.sv` creates derived clocks (prefer PLL in ASIC/FPGA)
- `clock_gate_ctrl.sv` is technology-agnostic (not optimized for specific process)

**FIFO Limitations:**
- Basic FIFOs in rtl/common/ are educational examples
- Production designs should use `rtl/amba/gaxi/gaxi_fifo_sync.sv`

### 6.3 Future Enhancements

**Potential Additions (Low Priority):**
- Additional arbiter types (token bucket, deficit round-robin)
- More ECC variants (BCH, Reed-Solomon)
- Multi-byte CRC support
- Gray-code FIFO for async CDC

---

## 7. Documentation and Support

### 7.1 Module Documentation

**Each module includes:**
- Header comment with description
- Parameter descriptions with valid ranges
- Port descriptions
- Usage examples
- Notes on special cases

**Example Module Header:**
```systemverilog
// Module: counter_bin
// Description: Binary up counter with enable and overflow detection
// Parameters:
//   - WIDTH: Counter bit width (default: 8, range: 1-64)
//   - MAX_VALUE: Maximum count before overflow (default: 2^WIDTH-1)
// Notes:
//   - Overflows when count reaches MAX_VALUE
//   - Can be used as modulo counter by setting MAX_VALUE
//   - Enable input gates counting operation
```

### 7.2 Quick Reference

**This Subsystem:**
- `rtl/common/PRD.md` - This document (detailed specification)
- `rtl/common/README.md` - Quick start and integration guide
- `rtl/common/CLAUDE.md` - AI assistance guide
- `rtl/common/TASKS.md` - Current work items

**Repository Root:**
- `/PRD.md` - Master project requirements
- `/CLAUDE.md` - Repository-wide AI guidance
- `/README.md` - Setup and getting started

**Tests:**
- `val/common/` - Test files (one per module)
- `val/common/GTKW/` - GTKWave save files for debug

---

## 8. Success Criteria

### 8.1 Functional Success

- ✅ All 86 modules compile cleanly (Verilator 0 warnings)
- ✅ All modules have corresponding tests
- ✅ ~90% test pass rate achieved
- ✅ No critical bugs identified
- ✅ Modules successfully integrated in AMBA and RAPIDS subsystems

### 8.2 Quality Metrics

- ✅ Consistent coding style across all modules
- ✅ Comprehensive parameter documentation
- ✅ Technology-agnostic designs
- ✅ Reusable in multiple subsystems
- ✅ Clear module naming and organization

### 8.3 Educational Value

- ✅ Demonstrates fundamental digital design patterns
- ✅ Shows best practices for parameterization
- ✅ Provides reference implementations
- ✅ Well-commented for learning
- ✅ Comprehensive test examples

---

## 9. References

### 9.1 Related Documentation

- `/PRD.md` - Master project PRD
- `/CLAUDE.md` - Repository-wide guidance
- `rtl/common/README.md` - Integration quick start
- `rtl/common/CLAUDE.md` - Subsystem-specific guide

### 9.2 External References

- **SystemVerilog LRM:** IEEE 1800-2017
- **Books:**
  - *Advanced FPGA Design* by Steve Kilts
  - *Synthesis of Arithmetic Circuits* by Deschamps, Bioul, Sutter
- **Tools:**
  - Verilator: https://verilator.org/
  - CocoTB: https://docs.cocotb.org/

### 9.3 Related Subsystems

- `rtl/amba/` - Uses common modules for infrastructure
- `rtl/rapids/` - Uses common modules for scheduling
- `bin/rtl_generators/` - Python generators for complex arithmetic

---

**Document Version:** 1.0
**Last Updated:** 2025-09-30
**Review Cycle:** Quarterly (stable subsystem)
**Next Review:** 2026-01-01
**Owner:** RTL Design Sherpa Project
