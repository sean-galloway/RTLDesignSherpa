# BCH Error Correction Code

**Version:** 0.1
**Status:** 📋 Future Project - Structure Created
**Last Updated:** 2025-10-29
**Purpose:** Configurable BCH (Bose-Chaudhuri-Hocquenghem) encoder and decoder for error correction

---

## Overview

BCH (Bose-Chaudhuri-Hocquenghem) codes are a class of cyclic error-correcting codes that are widely used in storage systems, communications, and digital signal processing. This component provides production-quality, configurable BCH encoder and decoder implementations suitable for both FPGA and ASIC deployment.

**Key Applications:**
- NAND flash memory error correction
- Solid-state drives (SSDs)
- Optical storage (CD, DVD, Blu-ray)
- Wireless communications (WiMAX, DVB, etc.)
- Deep space communications
- Data integrity in high-reliability systems

---

## BCH Code Fundamentals

### What is BCH?

BCH codes are a generalization of Hamming codes that can correct multiple random errors in a block of data. A BCH code is specified by three parameters: **BCH(n, k, t)**

- **n**: Codeword length (total bits after encoding)
- **k**: Message length (information bits before encoding)
- **t**: Error correction capability (number of errors that can be corrected)
- **Parity bits**: n - k = 2t × m (where m is the Galois field parameter)

### Common BCH Configurations

| Configuration | n (codeword) | k (message) | t (errors) | Parity | Code Rate | Applications |
|---------------|--------------|-------------|------------|--------|-----------|--------------|
| BCH(511,493,2) | 511 | 493 | 2 | 18 | 0.965 | Flash memory |
| BCH(1023,1013,2) | 1023 | 1013 | 2 | 10 | 0.990 | High-rate communications |
| BCH(2047,2007,5) | 2047 | 2007 | 5 | 40 | 0.980 | Optical storage |
| BCH(4095,4079,2) | 4095 | 4079 | 2 | 16 | 0.996 | High-speed serial links |
| BCH(8191,8171,2) | 8191 | 8171 | 2 | 20 | 0.998 | Ultra-high-rate systems |

### Error Correction Capability

- **t = 1**: Corrects 1 error per codeword (similar to Hamming code)
- **t = 2**: Corrects 2 errors per codeword (common in NAND flash)
- **t = 4-8**: Corrects 4-8 errors (typical in SSDs)
- **t = 16-40**: Corrects many errors (deep space communications, high-reliability)

---

## Planned Features

### BCH Encoder
- Configurable BCH(n, k, t) parameters
- Systematic encoding (message bits unchanged, parity appended)
- LFSR-based implementation (low latency, high throughput)
- Parallel processing options (bit-serial, byte-parallel, word-parallel)
- Pipeline-friendly architecture
- Generator polynomial configuration
- Support for multiple standard configurations

### BCH Decoder
- Syndrome calculation (parallel or serial)
- Error locator polynomial computation (Berlekamp-Massey or Euclidean algorithm)
- Chien search for error location finding
- Error magnitude calculation (for non-binary BCH)
- Error correction logic
- Uncorrectable error detection
- Configurable latency/area trade-offs
- Optional error statistics output

### Interface Options
- AXI4-Stream interface (standard for streaming data)
- Simple valid/ready handshake
- Burst mode support
- Configurable data width (8, 16, 32, 64 bits)
- Optional metadata passthrough
- Error statistics interface

### Advanced Features (Future)
- Multi-rate configurations (switch between BCH codes on-the-fly)
- Iterative decoding for improved performance
- Soft-decision decoding (for channel applications)
- Low-power modes
- Built-in self-test (BIST) for verification

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                       BCH Component                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                   │
│  ┌──────────────┐              ┌──────────────┐                 │
│  │              │   Encoded    │              │   Corrected     │
│  │  BCH Encoder │─────────────▶│  BCH Decoder │─────────────▶   │
│  │              │   Codeword   │              │   Data          │
│  └──────────────┘              └──────────────┘                 │
│         ▲                              │                         │
│         │                              │                         │
│     Data Input                    Error Stats                   │
│     (k bits)                      (errors corrected,             │
│                                    uncorrectable)                │
│                                                                   │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │  Encoder: LFSR with generator polynomial g(x)              │ │
│  │  Decoder: Syndrome → BM/Euclidean → Chien → Correction    │ │
│  └────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

### BCH Encoder Flow
1. Input k-bit message
2. Calculate parity using generator polynomial g(x)
3. Append parity bits to message (systematic encoding)
4. Output n-bit codeword

### BCH Decoder Flow
1. Input n-bit received codeword (possibly with errors)
2. Calculate syndromes S_1, S_2, ..., S_2t
3. Solve key equation for error locator polynomial σ(x) using Berlekamp-Massey or Euclidean algorithm
4. Find error locations using Chien search
5. Correct errors in received data
6. Output corrected k-bit message

---

## Directory Structure

```
bch/
├── rtl/                        # RTL source code
│   ├── encoder/               # BCH encoder modules
│   │   ├── bch_encoder.sv     # Top-level encoder
│   │   ├── bch_lfsr.sv        # LFSR for parity generation
│   │   └── bch_genpoly.sv     # Generator polynomial ROM
│   ├── decoder/               # BCH decoder modules
│   │   ├── bch_decoder.sv     # Top-level decoder
│   │   ├── bch_syndrome.sv    # Syndrome calculator
│   │   ├── bch_berlekamp.sv   # Berlekamp-Massey algorithm
│   │   ├── bch_chien.sv       # Chien search
│   │   └── bch_corrector.sv   # Error correction logic
│   ├── common/                # Shared modules
│   │   ├── gf_mult.sv         # Galois field multiplier
│   │   ├── gf_add.sv          # Galois field adder
│   │   └── gf_inv.sv          # Galois field inverse
│   └── top/                   # Top-level wrappers
│       ├── bch_codec.sv       # Combined encoder + decoder
│       └── bch_axis_wrapper.sv # AXI4-Stream interface wrapper
│
├── dv/                         # Design Verification
│   ├── tbclasses/             # Testbench classes
│   │   ├── bch_encoder_tb.py
│   │   ├── bch_decoder_tb.py
│   │   └── bch_codec_tb.py
│   ├── tests/                 # Test runners
│   │   ├── test_bch_encoder.py
│   │   ├── test_bch_decoder.py
│   │   └── test_bch_codec.py
│   ├── components/            # Test components (error injectors, etc.)
│   └── scoreboards/           # Verification scoreboards
│
├── docs/                       # Documentation
│   ├── bch_spec/              # BCH specification
│   ├── theory/                # Mathematical background
│   └── examples/              # Usage examples
│
├── bin/                        # Tools and utilities
│   ├── bch_genpoly_gen.py     # Generator polynomial calculator
│   ├── bch_params.py          # BCH parameter calculator
│   └── bch_model.py           # Python reference model
│
├── known_issues/              # Issue tracking
│   ├── active/
│   └── resolved/
│
├── PRD.md                      # Product Requirements Document
├── CLAUDE.md                   # AI assistant guide
├── TASKS.md                    # Task tracking
└── README.md                   # This file
```

---

## Design Philosophy

### 1. Configurability
- Support multiple BCH configurations via parameters
- Easy switching between standard codes
- Flexible data widths and interfaces

### 2. Performance
- High-throughput encoder (1 bit per cycle or better)
- Pipelined decoder architecture
- Low-latency syndrome calculation
- Parallel Chien search options

### 3. Area Efficiency
- Shared Galois field arithmetic units
- Configurable parallelism (trade latency for area)
- Optional ROM vs. computation trade-offs

### 4. Verification
- Comprehensive testbenches with random error injection
- Reference model comparison
- Corner case testing (max errors, error-free, uncorrectable)
- Performance characterization

---

## Use Cases

### Flash Memory Error Correction
```systemverilog
bch_codec #(
    .N(1023),      // Codeword length
    .K(1013),      // Message length
    .T(2),         // Correct 2 errors
    .M(10)         // GF(2^10)
) u_flash_ecc (
    .clk          (clk),
    .rst_n        (rst_n),
    .encode_mode  (write_operation),
    .data_in      (flash_data),
    .data_valid   (data_valid),
    .data_ready   (data_ready),
    .data_out     (corrected_data),
    .error_count  (errors_detected),
    .uncorrectable(uncorrectable_error)
);
```

### High-Speed Communications
```systemverilog
bch_axis_wrapper #(
    .N(511),
    .K(493),
    .T(2),
    .DATA_WIDTH(64)    // 64-bit parallel processing
) u_comms_ecc (
    .axis_aclk       (clk),
    .axis_aresetn    (rst_n),
    // AXI4-Stream slave (input)
    .s_axis_tdata    (rx_data),
    .s_axis_tvalid   (rx_valid),
    .s_axis_tready   (rx_ready),
    // AXI4-Stream master (output)
    .m_axis_tdata    (tx_data),
    .m_axis_tvalid   (tx_valid),
    .m_axis_tready   (tx_ready),
    .m_axis_tuser    (error_status)
);
```

---

## Development Roadmap

### Phase 1: Encoder (3-4 weeks)
- [ ] BCH parameter calculator tool
- [ ] Generator polynomial generation
- [ ] LFSR-based encoder implementation
- [ ] Encoder testbench
- [ ] Support for BCH(511,493,2) and BCH(1023,1013,2)

### Phase 2: Decoder Foundation (6-8 weeks)
- [ ] Galois field arithmetic modules
- [ ] Syndrome calculator
- [ ] Berlekamp-Massey algorithm
- [ ] Chien search implementation
- [ ] Error correction logic

### Phase 3: Integration (3-4 weeks)
- [ ] Combined encoder/decoder wrapper
- [ ] AXI4-Stream interface
- [ ] Error statistics
- [ ] System testbench

### Phase 4: Optimization (4-6 weeks)
- [ ] Parallel processing options
- [ ] Pipelined decoder
- [ ] Area optimization
- [ ] Performance characterization

### Phase 5: Extended Configurations (4-6 weeks)
- [ ] Support for t=4, 8, 16
- [ ] Larger codewords (n > 8191)
- [ ] Multi-rate configuration
- [ ] Advanced features

---

## Key Challenges

### Galois Field Arithmetic
- Efficient implementation of GF(2^m) operations
- Multiplier optimization (area vs. speed)
- Inverse calculation (for Berlekamp-Massey)

### Decoder Complexity
- Berlekamp-Massey requires iterative computation
- Chien search requires parallel evaluation
- Error correction requires precise timing

### Verification
- Exhaustive testing infeasible for large codes
- Random error injection must cover all cases
- Corner cases: all-zeros, all-ones, maximum correctable errors

---

## References

### Theory
- Lin, S., & Costello, D. J. (2004). *Error Control Coding* (2nd ed.)
- Wicker, S. B. (1995). *Error Control Systems for Digital Communication and Storage*
- Blahut, R. E. (2003). *Algebraic Codes for Data Transmission*

### Standards
- IEEE 802.16e (WiMAX) - Uses BCH codes
- DVB-S2 (Digital Video Broadcasting) - BCH outer code
- NAND Flash Memory - Various BCH configurations

### Implementation
- Berlekamp, E. R. (1968). *Algebraic Coding Theory*
- Massey, J. L. (1969). "Shift-register synthesis and BCH decoding"
- Reed, I. S., & Solomon, G. (1960). "Polynomial Codes Over Certain Finite Fields"

---

## Getting Started

### For Users
This component is currently in planning phase. Check back for updates!

### For Developers
See `PRD.md` for detailed requirements and `CLAUDE.md` for development guidance.

---

## Status

- 📋 **Phase:** Future Project - Structure Created
- ❌ **RTL:** Not started
- ❌ **Tests:** Not started
- ❌ **Docs:** Planning phase

**Next Steps:**
1. Create PRD.md with detailed specifications
2. Develop Python reference model
3. Implement basic encoder for BCH(511,493,2)
4. Create encoder testbench

---

**Version:** 0.1 (Structure Created)
**Last Updated:** 2025-10-29
**Maintained By:** RTL Design Sherpa Project
