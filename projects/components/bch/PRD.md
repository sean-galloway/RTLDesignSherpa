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

# BCH Error Correction Code - Product Requirements Document

**Component:** BCH (Bose-Chaudhuri-Hocquenghem) Error Correction
**Version:** 0.1
**Status:** 📋 Future Project - Planning Phase
**Last Updated:** 2025-10-29

---

## 1. Overview

### 1.1 Purpose

Provide production-quality, configurable BCH encoder and decoder implementations for error correction in storage systems, communications, and high-reliability applications.

### 1.2 Scope

**In Scope:**
- Configurable BCH encoder (systematic encoding)
- Configurable BCH decoder (syndrome-based hard-decision decoding)
- Support for binary BCH codes over GF(2^m)
- Common configurations (t=1,2,4,8,16)
- AXI4-Stream and simple handshake interfaces
- Comprehensive verification and reference models

**Out of Scope (Future):**
- Non-binary BCH codes (Reed-Solomon covered separately)
- Soft-decision decoding
- Concatenated codes (handled at system level)
- Hardware-accelerated key equation solvers beyond Berlekamp-Massey/Euclidean

### 1.3 Target Applications

**Primary:**
- NAND flash memory error correction
- Solid-state drives (SSDs)
- High-speed serial communications
- Optical storage systems

**Secondary:**
- Wireless communications (WiMAX, DVB)
- Deep space communications
- Safety-critical systems (automotive, aerospace)
- Data integrity in compute systems

---

## 2. BCH Code Theory

### 2.1 Mathematical Foundation

A BCH code is a cyclic code over GF(2) with symbols from GF(2^m).

**Generator Polynomial:**
```
g(x) = LCM(m_1(x), m_3(x), ..., m_{2t-1}(x))
```
where m_i(x) is the minimal polynomial of α^i, and α is a primitive element of GF(2^m).

**Code Parameters:**
- **n**: Codeword length = 2^m - 1
- **k**: Message length = n - deg(g(x))
- **t**: Error correction capability
- **m**: Galois field parameter

**Relation:**
```
deg(g(x)) ≤ m × t
n - k ≤ m × t
```

### 2.2 Standard Configurations

| Config | n | k | t | m | Parity | Rate | Use Case |
|--------|---|---|---|---|--------|------|----------|
| BCH(7,4,1) | 7 | 4 | 1 | 3 | 3 | 0.571 | Tutorial/test |
| BCH(15,11,1) | 15 | 11 | 1 | 4 | 4 | 0.733 | Simple ECC |
| BCH(31,26,1) | 31 | 26 | 1 | 5 | 5 | 0.839 | Low overhead |
| BCH(63,57,1) | 63 | 57 | 1 | 6 | 6 | 0.905 | Moderate rate |
| BCH(127,120,1) | 127 | 120 | 1 | 7 | 7 | 0.945 | High rate |
| BCH(255,247,1) | 255 | 247 | 1 | 8 | 8 | 0.969 | Very high rate |
| BCH(511,493,2) | 511 | 493 | 2 | 9 | 18 | 0.965 | Flash memory |
| BCH(1023,1013,2) | 1023 | 1013 | 2 | 10 | 10 | 0.990 | Communications |
| BCH(2047,2007,5) | 2047 | 2007 | 5 | 11 | 40 | 0.980 | Optical storage |
| BCH(4095,4057,4) | 4095 | 4057 | 4 | 12 | 38 | 0.991 | High-speed links |

### 2.3 Error Correction Performance

**Probability of Undetected Error:**
For t-error-correcting BCH code and channel bit error rate p:

```
P_undetected ≈ Σ(i=t+1 to n) C(n,i) × p^i × (1-p)^(n-i)
```

**Example (BCH(511,493,2), p=10^-6):**
- Corrects up to 2 errors per 511-bit block
- P_undetected < 10^-15 (extremely low)

---

## 3. Functional Requirements

### 3.1 BCH Encoder

#### 3.1.1 Core Functionality

**FR-ENC-001: Systematic Encoding**
- Encoder SHALL implement systematic encoding
- Message bits SHALL remain unchanged in output
- Parity bits SHALL be appended to message
- Output format: [message(k bits) | parity(n-k bits)]

**FR-ENC-002: Configurable Parameters**
- Encoder SHALL support configurable (n, k, t, m) parameters
- Parameters SHALL be compile-time configuration (Verilog parameters)
- Runtime configuration optional for future multi-rate support

**FR-ENC-003: Generator Polynomial**
- Encoder SHALL use generator polynomial g(x) specific to BCH(n, k, t)
- Polynomial MAY be stored in ROM or computed at compile-time
- Polynomial coefficients SHALL be derived from minimal polynomials

**FR-ENC-004: LFSR Implementation**
- Encoder SHALL implement LFSR-based division algorithm
- LFSR SHALL have length equal to degree of g(x)
- LFSR SHALL process bits serially or in parallel

#### 3.1.2 Performance

**FR-ENC-005: Throughput**
- Bit-serial encoder SHALL process 1 bit per clock cycle minimum
- Parallel encoder SHALL process N bits per clock cycle (N configurable: 8, 16, 32, 64)
- Encoder latency SHALL be ≤ n clock cycles for bit-serial, ≤ n/N for parallel

**FR-ENC-006: Latency**
- Encoder latency SHALL be deterministic
- Pipeline depth SHALL be configurable (area vs. latency trade-off)

#### 3.1.3 Interfaces

**FR-ENC-007: Input Interface**
- Encoder SHALL accept k-bit message
- Interface SHALL support valid/ready handshake
- Backpressure SHALL be supported

**FR-ENC-008: Output Interface**
- Encoder SHALL output n-bit codeword
- Interface SHALL support valid/ready handshake
- Output SHALL be synchronous to input clock

### 3.2 BCH Decoder

#### 3.2.1 Core Functionality

**FR-DEC-001: Syndrome Calculation**
- Decoder SHALL calculate 2t syndromes S_1, S_2, ..., S_2t
- Syndromes SHALL be computed over GF(2^m)
- Syndrome calculation MAY be parallel or serial

**FR-DEC-002: Error Locator Polynomial**
- Decoder SHALL solve key equation for error locator polynomial σ(x)
- Implementation SHALL use Berlekamp-Massey algorithm OR Euclidean algorithm
- Polynomial degree SHALL be ≤ t

**FR-DEC-003: Chien Search**
- Decoder SHALL find error locations using Chien search
- Search SHALL evaluate σ(x) at all n positions
- Search MAY be implemented in parallel or serial

**FR-DEC-004: Error Correction**
- Decoder SHALL flip bits at error locations (binary BCH)
- Decoder SHALL output corrected k-bit message
- Original parity bits MAY be discarded or passed through

**FR-DEC-005: Error Detection**
- Decoder SHALL detect when number of errors > t (uncorrectable)
- Decoder SHALL indicate uncorrectable error condition
- Decoder SHALL output uncorrected data when uncorrectable

#### 3.2.2 Performance

**FR-DEC-006: Throughput**
- Decoder throughput SHALL be configurable based on parallelism
- Minimum throughput target: 1 Gbps for BCH(511,493,2) @ 100 MHz
- Decoder latency SHALL be ≤ 10 × n clock cycles

**FR-DEC-007: Error Statistics**
- Decoder SHALL output number of errors corrected
- Decoder SHALL flag uncorrectable errors
- Optional: Syndrome zero detection (error-free fast path)

#### 3.2.3 Galois Field Arithmetic

**FR-DEC-008: GF Operations**
- Decoder SHALL implement GF(2^m) addition (XOR)
- Decoder SHALL implement GF(2^m) multiplication
- Decoder SHALL implement GF(2^m) inversion (for Berlekamp-Massey)
- Arithmetic units MAY be shared or replicated for parallelism

**FR-DEC-009: Field Configuration**
- GF(2^m) primitive polynomial SHALL be configurable
- Standard primitive polynomials SHALL be supported:
  - GF(2^4): x^4 + x + 1
  - GF(2^8): x^8 + x^4 + x^3 + x^2 + 1
  - GF(2^10): x^10 + x^3 + 1
  - GF(2^12): x^12 + x^6 + x^4 + x + 1

---

## 4. Interface Requirements

### 4.1 Encoder Interface

```systemverilog
module bch_encoder #(
    parameter int N = 511,          // Codeword length
    parameter int K = 493,          // Message length
    parameter int T = 2,            // Error correction capability
    parameter int M = 9,            // GF(2^M)
    parameter int DATA_WIDTH = 8    // Parallel processing width
) (
    input  logic                  clk,
    input  logic                  rst_n,

    // Input interface (message)
    input  logic                  s_valid,
    output logic                  s_ready,
    input  logic [DATA_WIDTH-1:0] s_data,
    input  logic                  s_last,    // Last symbol of message

    // Output interface (codeword)
    output logic                  m_valid,
    input  logic                  m_ready,
    output logic [DATA_WIDTH-1:0] m_data,
    output logic                  m_last     // Last symbol of codeword
);
```

### 4.2 Decoder Interface

```systemverilog
module bch_decoder #(
    parameter int N = 511,          // Codeword length
    parameter int K = 493,          // Message length
    parameter int T = 2,            // Error correction capability
    parameter int M = 9,            // GF(2^M)
    parameter int DATA_WIDTH = 8    // Parallel processing width
) (
    input  logic                  clk,
    input  logic                  rst_n,

    // Input interface (received codeword)
    input  logic                  s_valid,
    output logic                  s_ready,
    input  logic [DATA_WIDTH-1:0] s_data,
    input  logic                  s_last,

    // Output interface (corrected message)
    output logic                  m_valid,
    input  logic                  m_ready,
    output logic [DATA_WIDTH-1:0] m_data,
    output logic                  m_last,

    // Error statistics
    output logic [$clog2(T+1)-1:0] errors_corrected,
    output logic                   uncorrectable_error,
    output logic                   error_free          // Fast path indicator
);
```

### 4.3 AXI4-Stream Wrapper

```systemverilog
module bch_axis_wrapper #(
    parameter int N = 511,
    parameter int K = 493,
    parameter int T = 2,
    parameter int M = 9,
    parameter int DATA_WIDTH = 64
) (
    input  logic                  axis_aclk,
    input  logic                  axis_aresetn,

    input  logic                  encode_mode,  // 1=encode, 0=decode

    // AXI4-Stream slave (input)
    input  logic [DATA_WIDTH-1:0] s_axis_tdata,
    input  logic                  s_axis_tvalid,
    output logic                  s_axis_tready,
    input  logic                  s_axis_tlast,

    // AXI4-Stream master (output)
    output logic [DATA_WIDTH-1:0] m_axis_tdata,
    output logic                  m_axis_tvalid,
    input  logic                  m_axis_tready,
    output logic                  m_axis_tlast,
    output logic [7:0]            m_axis_tuser   // Error statistics
);
```

---

## 5. Design Standards

### 5.1 RTL Standards

**DS-001: Reset Macros**
- ALL modules SHALL use reset macros from `rtl/amba/includes/reset_defs.svh`
- Pattern: `ALWAYS_FF_RST(clk, rst_n, ...)`

**DS-002: FPGA Attributes**
- ALL memory arrays SHALL have FPGA synthesis attributes
- Pattern: `(* ram_style = "auto" *)` for Xilinx, `/* synthesis ramstyle = "AUTO" */` for Intel

**DS-003: Coding Style**
- Follow repository SystemVerilog style guide
- Use `logic` not `reg`/`wire`
- Explicit bit widths for all signals
- No latches (all combinational paths complete)

**DS-004: Finite Field Arithmetic**
- GF operations SHALL be in separate, reusable modules
- GF multiplier SHALL support both LUT and combinational implementations
- GF inverse SHALL use Fermat's little theorem or lookup table

### 5.2 Testbench Standards

**DS-005: Reference Model**
- Python reference model SHALL be implemented
- Reference model SHALL use NumPy/Galois library for field arithmetic
- All test vectors SHALL be cross-checked with reference model

**DS-006: Test Coverage**
- 100% line coverage for encoder
- >95% line coverage for decoder
- Functional coverage for all (n, k, t) configurations
- Corner cases: 0 errors, t errors, >t errors (uncorrectable)

**DS-007: Error Injection**
- Random error injection for decoder testing
- Configurable error patterns (single-bit, burst, random)
- Statistical validation of correction capability

---

## 6. Verification Requirements

### 6.1 Encoder Verification

**VR-ENC-001: Correctness**
- Encoded codewords SHALL match reference model
- Test with all-zeros, all-ones, random data
- Test with all supported configurations

**VR-ENC-002: Backpressure**
- Encoder SHALL handle input backpressure correctly
- Encoder SHALL handle output backpressure correctly
- No data loss or corruption during backpressure

**VR-ENC-003: Performance**
- Measure throughput for all configurations
- Verify latency meets requirements
- Characterize resource utilization (LUTs, FFs, BRAMs)

### 6.2 Decoder Verification

**VR-DEC-001: Error-Free Decoding**
- Decoder SHALL correctly decode error-free codewords
- Output SHALL exactly match input message
- Fast-path optimization SHALL work correctly

**VR-DEC-002: Error Correction**
- Decoder SHALL correct all error patterns with ≤ t errors
- Test with random error injection (10,000+ trials per config)
- Verify errors_corrected output is accurate

**VR-DEC-003: Uncorrectable Errors**
- Decoder SHALL flag uncorrectable errors (>t errors)
- Decoder SHALL NOT falsely correct >t errors
- Decoder SHALL output original data when uncorrectable

**VR-DEC-004: Syndrome Calculation**
- Syndrome values SHALL match reference model
- All-zero syndrome SHALL be detected for error-free codewords

**VR-DEC-005: Berlekamp-Massey**
- Error locator polynomial SHALL match reference model
- Polynomial degree SHALL be ≤ t
- Algorithm SHALL converge in ≤ 2t iterations

**VR-DEC-006: Chien Search**
- Error locations SHALL match reference model
- All error positions SHALL be found
- False positives SHALL NOT occur

---

## 7. Performance Targets

### 7.1 Encoder Performance

| Configuration | Throughput (Gbps) | Latency (cycles) | LUTs | FFs | BRAMs |
|---------------|-------------------|------------------|------|-----|-------|
| BCH(511,493,2) @ 100 MHz, 8-bit | 0.8 | <100 | <5K | <3K | 0 |
| BCH(511,493,2) @ 100 MHz, 64-bit | 6.4 | <20 | <15K | <8K | 0 |
| BCH(1023,1013,2) @ 200 MHz, 64-bit | 12.8 | <40 | <20K | <10K | 0 |

### 7.2 Decoder Performance

| Configuration | Throughput (Gbps) | Latency (cycles) | LUTs | FFs | BRAMs |
|---------------|-------------------|------------------|------|-----|-------|
| BCH(511,493,2) @ 100 MHz | 0.4 | <1000 | <30K | <15K | 2 |
| BCH(1023,1013,2) @ 200 MHz | 0.8 | <2000 | <50K | <25K | 4 |

**Note:** Performance targets are estimates and subject to revision based on implementation.

---

## 8. Development Phases

### Phase 1: Foundation (Weeks 1-4)
- [ ] BCH parameter calculator tool (Python)
- [ ] Generator polynomial generator
- [ ] Reference model implementation
- [ ] GF arithmetic modules (add, mult, inv)
- [ ] Basic encoder for BCH(7,4,1)

### Phase 2: Encoder (Weeks 5-8)
- [ ] LFSR-based encoder for standard configs
- [ ] Parallel encoder (8-bit, 64-bit)
- [ ] Encoder testbench
- [ ] Verification with reference model

### Phase 3: Decoder Foundation (Weeks 9-14)
- [ ] Syndrome calculator
- [ ] Berlekamp-Massey algorithm
- [ ] Chien search implementation
- [ ] Error correction logic
- [ ] Basic decoder testbench

### Phase 4: Integration (Weeks 15-18)
- [ ] Combined encoder/decoder wrapper
- [ ] AXI4-Stream interface
- [ ] Error statistics
- [ ] System-level testbench
- [ ] Random error injection testing

### Phase 5: Optimization (Weeks 19-22)
- [ ] Pipelined decoder
- [ ] Parallel Chien search
- [ ] Area optimization
- [ ] Performance characterization

### Phase 6: Documentation (Weeks 23-24)
- [ ] Complete specification
- [ ] User guide
- [ ] Integration examples
- [ ] Performance reports

**Total Estimated Effort:** 24 weeks (6 months)

---

## 9. Success Criteria

### 9.1 Functional Success
- ✅ Encoder produces correct codewords for all test vectors
- ✅ Decoder corrects all error patterns ≤ t errors
- ✅ Decoder flags uncorrectable errors (>t errors)
- ✅ No false corrections in 100,000+ random trials

### 9.2 Performance Success
- ✅ Encoder throughput meets targets
- ✅ Decoder throughput meets targets
- ✅ Resource utilization within estimates
- ✅ Timing closure @ target frequency

### 9.3 Verification Success
- ✅ 100% line coverage for encoder
- ✅ >95% line coverage for decoder
- ✅ All corner cases tested
- ✅ Statistical validation complete

### 9.4 Documentation Success
- ✅ Complete specification document
- ✅ User integration guide
- ✅ Performance characterization report
- ✅ Reference model documented

---

## 10. References

### 10.1 Books
1. Lin, S., & Costello, D. J. (2004). *Error Control Coding* (2nd ed.). Pearson.
2. Wicker, S. B. (1995). *Error Control Systems for Digital Communication and Storage*. Prentice Hall.
3. Blahut, R. E. (2003). *Algebraic Codes for Data Transmission*. Cambridge University Press.
4. Berlekamp, E. R. (1968). *Algebraic Coding Theory*. McGraw-Hill.

### 10.2 Papers
1. Massey, J. L. (1969). "Shift-register synthesis and BCH decoding." *IEEE Trans. Inf. Theory*, 15(1), 122-127.
2. Chien, R. (1964). "Cyclic decoding procedures for Bose-Chaudhuri-Hocquenghem codes." *IEEE Trans. Inf. Theory*, 10(4), 357-363.
3. Berlekamp, E. R. (1966). "Nonbinary BCH decoding." *IEEE Trans. Inf. Theory*, 12(2), 242-242.

### 10.3 Standards
- IEEE 802.16e-2005 (WiMAX) - Uses BCH codes
- ETSI EN 302 307 (DVB-S2) - BCH outer code specification
- JEDEC JESD218 (NAND Flash) - BCH ECC requirements

### 10.4 Open Source References
- GNU Radio: gr-fec BCH encoder/decoder
- Linux kernel: BCH library (lib/bch.c)
- Galois library (Python): https://github.com/mhostetter/galois

---

**Version:** 0.1 (Planning Phase)
**Last Updated:** 2025-10-29
**Next Review:** After Phase 1 completion
**Maintained By:** RTL Design Sherpa Project
