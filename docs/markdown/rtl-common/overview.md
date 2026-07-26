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

**[← Back to Main Index](../index.md)** | **[rtl-common Index](index.md)**

# rtl-common Library Overview

The rtl-common library is a collection of fundamental digital design building blocks — parameterizable, synthesis-friendly RTL modules built to a consistent quality bar, ready to drop into a wide range of digital systems.

## Library Philosophy

### Design Principles

The library is built on a handful of core principles:

**Modularity**: Each module does one specific function and composes easily with the others
**Parameterizability**: Configurable width and functionality parameters for maximum reusability
**Synthesis Friendly**: Optimized for modern synthesis tools with predictable area/timing results
**Technology Independence**: Clean RTL that works across ASIC and FPGA technologies
**Broad Coverage**: counters, FIFOs, arbiters, CDC, data integrity, and clock/reset control (arithmetic is its own library — [rtl-math](../rtl-math/index.md))

### Quality Standards

- **Lint Clean**: All modules pass rigorous RTL linting checks
- **Simulation Verified**: Comprehensive testbenches validate functionality
- **Synthesizable**: Written in standard SystemVerilog with no vendor primitives
- **Documentation Complete**: Detailed documentation with usage examples

## Architecture Overview

### Module Hierarchy

Per-category counts live in one place — the [count table in index.md](index.md#module-count-by-category) — so this tree lists categories only and cannot drift from it.


```
rtl-common Library
├── (Arithmetic & Math moved to rtl/math/ — see rtl-math book)
├── Data Integrity
│   ├── Error Detection (CRC, Checksum, Parity)
│   └── Error Correction (Hamming ECC)
├── Control & Arbitration
│   ├── Round-Robin Arbiters
│   └── Priority Arbiters
├── Clock & Reset
│   ├── Clock Management (ICG, Dividers)
│   └── Reset Synchronization
├── Counters & Sequences
│   ├── Binary & Gray Code Counters
│   └── Specialized Counting
├── Data Conversion
│   ├── Code Converters (Binary/Gray/BCD)
│   └── Display Decoders
├── Bit Operations
│   ├── Bit Searching & Counting
│   └── Vector Manipulation
├── Shift & LFSR
│   ├── Barrel Shifters
│   └── Pseudorandom Generation
├── Memory & Storage
│   ├── FIFO Implementations
│   └── Content Addressable Memory
└── Utilities
    ├── PWM Generation
    └── Sorting Algorithms
```

## Functional Categories

### 1. Arithmetic and Mathematical Operations

**Moved.** The `math_*` arithmetic library (adders, subtractors, multipliers,
compressors, prefix cells, and the BF16 / FP8 / FP16 / FP32 / IEEE-754
floating-point modules) is now its own subsystem and its own book:
**[rtl-math](../rtl-math/index.md)** — RTL in `rtl/math/`, tests in `val/math/`.

### 2. Data Integrity and Error Management

These blocks are critical for reliable data storage and transmission in modern digital systems.

#### Cyclic Redundancy Check (CRC)
- **Generic CRC Engine**: Configurable polynomial, width, and initialization
- **Cascade Implementation**: High-throughput parallel CRC processing
- **XOR-Shift Variants**: Optimized for specific polynomial types

#### Error Correction Coding (ECC)
- **Hamming SECDED**: Single Error Correction, Double Error Detection
- **Configurable Width**: Support for various data widths
- **Encoder/Decoder Pairs**: Complete ECC implementation

#### Simple Integrity Checks
- **Checksum**: Software-compatible checksum algorithms
- **Parity**: Even/odd parity generation and checking

**Key Features:**
- Standards-compliant implementations
- Parameterizable for various data widths
- Optimized for both latency and throughput scenarios

### 3. Control Logic and Arbitration

Shared resources need a referee. These are the essential components for managing them and coordinating the system.

#### Round-Robin Arbitration
- **Simple Round-Robin**: Basic fair arbitration with minimal overhead
- **Weighted Round-Robin**: Priority-based fair arbitration
- **Advanced Features**: Configurable agent counts and weighting

#### Priority-Based Control
- **Priority Encoders**: Fixed priority arbitration schemes
- **Configurable Priority**: Runtime priority adjustment capability

**Applications:**
- Bus arbitration in multi-master systems
- Resource allocation in processors
- Quality of Service (QoS) implementations

### 4. Clock and Reset Management

Power and timing management — the unglamorous foundation of a dependable digital system design.

#### Clock Control
- **Integrated Clock Gating (ICG)**: Power optimization through controlled clock disabling
- **Clock Dividers**: Frequency synthesis and clock domain generation
- **Pulse Generators**: Controlled clock pulse generation

#### Reset and Synchronization
- **Reset Synchronizers**: Safe reset assertion/deassertion
- **Glitch-Free Logic**: Reliable signal conditioning
- **Debouncing**: Input signal stabilization

**Power Management Benefits:**
- Clock gating (ICG) removes switching on idle functional blocks; the actual
  dynamic-power saving depends on activity factor and is design-specific
- Proper reset sequencing for reliable startup
- Signal integrity maintenance

### 5. Counting and Sequence Generation

Fundamental building blocks for timing, addressing, and control.

#### Binary Counters
- **Basic Counters**: Up/down counting with enable/reset
- **Gray Code Counters**: Glitch-free counting for async interfaces
- **Johnson Counters**: Shift-based sequence generation

#### Specialized Counting
- **Frequency-Invariant**: Clock-independent counting
- **Load/Clear**: Programmable counter initialization
- **Ring Counters**: One-hot sequence generation

**Design Features:**
- Parameterizable width and functionality
- Optional synchronous/asynchronous controls
- Overflow/underflow detection

### 6. Data Conversion and Encoding

Code conversion and display interfacing utilities.

#### Number System Conversion
- **Binary ↔ Gray**: Safe async counter interfacing
- **Binary → BCD**: Decimal display conversion
- **Johnson Gray**: Specialized counting applications

#### Encoding/Decoding
- **Priority Encoders**: Multiple input to binary conversion
- **Binary Decoders**: Address decoding and control
- **7-Segment Display**: Hexadecimal character display

**Applications:**
- Display interfaces
- Address decoding
- Safe async signal crossing

### 7. Bit Manipulation and Searching

Efficient bit-level operations for high-performance computing.

#### Bit Detection
- **Leading Zero Count**: Normalization and floating-point support
- **Find First/Last Set**: Efficient bit searching
- **Priority Detection**: Leading one and trailing one detection

#### Vector Operations
- **Bit Reversal**: Endianness conversion and FFT applications
- **Vector Manipulation**: Bit-level data reorganization

**Performance Characteristics:**
- Logarithmic complexity algorithms where possible
- Optimized for synthesis tool recognition
- Support for various data widths

### 8. Shift Operations and LFSRs

Shift-based operations and pseudorandom sequence generation.

#### Shifters
- **Barrel Shifters**: Arbitrary shift/rotate in single cycle
- **Universal Shifters**: Combined left/right, logical/arithmetic shifting

#### Linear Feedback Shift Registers (LFSRs)
- **Fibonacci LFSRs**: External feedback topology
- **Galois LFSRs**: Internal feedback topology
- **Configurable Polynomials**: Various sequence lengths and properties

**Applications:**
- Pseudorandom number generation
- Built-in self-test (BIST) patterns
- Encryption and scrambling

### 9. Memory and Storage

Buffering and storage solutions for data flow management.

#### FIFO Implementations
- **Synchronous FIFO**: Single clock domain buffering
- **Asynchronous FIFO**: Clock domain crossing with Gray code pointers
- **Specialized FIFOs**: Optimized for specific clock relationships

#### Associative Memory
- **Content Addressable Memory (CAM)**: Tag matching and lookup

**Features:**
- Configurable depth and width
- Full/empty flag generation
- Error handling and overflow protection

### 10. Utility and Specialized Functions

Specialized functions for specific application domains.

#### Signal Generation
- **PWM**: Pulse width modulation for analog control
- **Timing Control**: Precise pulse and timing generation

#### Data Processing
- **Hardware Sorting**: Parallel sorting implementations
- **Algorithmic Processing**: Specialized computational functions

## Performance and Optimization

### Synthesis Guidelines

#### Area Optimization
- Use ripple-carry arithmetic for low-area requirements
- Select appropriate FIFO depths based on data flow analysis
- Consider shared resources for infrequently used functions

#### Speed Optimization
- Use parallel prefix adders (Kogge-Stone) for critical paths
- Implement pipelining in high-throughput applications
- Utilize barrel shifters for single-cycle shift operations

#### Power Optimization
- Apply clock gating (ICG) to inactive functional blocks
- Use Gray code counters for reduced switching activity
- Implement frequency-invariant designs where applicable

### Technology-Specific Considerations

#### ASIC Implementation
- Use dedicated adder and multiplier cells
- Use technology-specific clock gating cells
- Optimize for specific voltage and temperature ranges

#### FPGA Implementation
- Use DSP blocks for arithmetic operations
- Use BRAM for deep FIFOs
- Use the dedicated clock management resources

## Verification and Validation

### Testbench Coverage
- **Functional Coverage**: All operational modes and edge cases
- **Directed Tests**: Specific functionality verification
- **Random Testing**: Stress testing with random inputs
- **Corner Cases**: Boundary conditions and error scenarios

### Compliance Testing
- **Timing Analysis**: Setup/hold requirements validation
- **Power Analysis**: Dynamic and static power characterization
- **Area Analysis**: Resource utilization across technologies

## Usage Guidelines

### Module Selection
1. **Identify Requirements**: Performance, area, and power constraints
2. **Select Architecture**: Choose appropriate implementation (ripple vs. parallel, etc.)
3. **Configure Parameters**: Set widths and options for specific application
4. **Verify Integration**: Ensure proper interfacing and timing

### Integration Best Practices
> The example below instantiates `math_adder_full_nbit`, which now lives in
> [`rtl/math/`](../rtl-math/index.md) — modules compose across the two libraries.

```systemverilog
// Example: Building a complete arithmetic unit (math_* modules are in rtl/math/)
module arithmetic_unit #(
    parameter int DATA_WIDTH = 32
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic [DATA_WIDTH-1:0]   operand_a,
    input  logic [DATA_WIDTH-1:0]   operand_b,
    input  logic [1:0]              operation,
    output logic [DATA_WIDTH-1:0]   result,
    output logic                    overflow
);

    // Use appropriate math modules based on requirements
    logic [DATA_WIDTH-1:0] add_result, sub_result, mult_result;
    logic add_carry, sub_borrow;

    // High-speed addition using parallel prefix
    math_adder_full_nbit #(
        .N(DATA_WIDTH)
    ) u_adder (
        .a(operand_a), .b(operand_b), .cin(1'b0),
        .sum(add_result), .cout(add_carry)
    );

    // Subtraction using complement method
    math_subtractor_full_nbit #(
        .N(DATA_WIDTH)
    ) u_subtractor (
        .a(operand_a), .b(operand_b), .bin(1'b0),
        .diff(sub_result), .bout(sub_borrow)
    );

    // Result selection based on operation
    always_comb begin
        case (operation)
            2'b00: begin result = add_result; overflow = add_carry; end
            2'b01: begin result = sub_result; overflow = sub_borrow; end
            default: begin result = '0; overflow = 1'b0; end
        endcase
    end

endmodule
```

## Future Enhancements

### Planned Additions
- **DSP Functions**: FFT, filtering, and signal processing primitives
- **Security Primitives**: Hardware security modules and cryptographic functions
- **AI/ML Accelerators**: Matrix operations and neural network primitives

### Technology Evolution
- **Emerging Technologies**: Support for new process nodes and device types
- **Tool Integration**: Enhanced synthesis and verification tool compatibility
- **Standards Compliance**: Updates for evolving industry standards

Taken together, the rtl-common library is a foundation for digital design: the building blocks you need to implement complex digital systems with confidence in their correctness, performance, and manufacturability.
