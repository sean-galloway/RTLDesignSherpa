# RTLCommon Modules Index

This directory contains documentation for the common RTL modules library, providing fundamental building blocks for digital design including arithmetic operations, data integrity functions, control logic, and specialized utilities.

## Overview

- **[Overview](overview.md)** - Complete overview of the RTLCommon library architecture and design philosophy

## Module Categories

### Arithmetic and Math Operations

#### Basic Arithmetic
- **[math_adder_basic](math_adder_basic.md)** - Single-bit adders (full and half adder)
  - Includes: `math_adder_full.sv`, `math_adder_half.sv`, `math_adder_full_nbit.sv`
- **[math_adder_ripple_carry](math_adder_ripple_carry.md)** - Multi-bit ripple carry adder
- **[math_adder_carry_lookahead](math_adder_carry_lookahead.md)** - Fast carry lookahead adder
- **[math_adder_carry_save](math_adder_carry_save.md)** - Carry-save adder for multiple operands
  - Includes: `math_adder_carry_save.sv`, `math_adder_carry_save_nbit.sv`
- **[math_adder_kogge_stone](math_adder_kogge_stone.md)** - High-speed Kogge-Stone parallel prefix adder
  - Includes: `math_adder_kogge_stone_nbit.sv`

#### Advanced Adders
- **[math_adder_brent_kung](math_adder_brent_kung.md)** - Brent-Kung parallel prefix adder family (8/16/32-bit)
  - Includes: `math_adder_brent_kung_008.sv`, `math_adder_brent_kung_016.sv`, `math_adder_brent_kung_032.sv`
  - Sub-modules: `math_adder_brent_kung_pg.sv`, `math_adder_brent_kung_black.sv`, `math_adder_brent_kung_gray.sv`, `math_adder_brent_kung_bitwisepg.sv`, `math_adder_brent_kung_grouppg_*.sv`, `math_adder_brent_kung_sum.sv`
- **[math_adder_han_carlson](math_adder_han_carlson.md)** - Han-Carlson hybrid parallel prefix adder (16/48-bit)
  - Includes: `math_adder_han_carlson_016.sv`, `math_adder_han_carlson_048.sv`
  - Building blocks: `math_prefix_cell.sv`, `math_prefix_cell_gray.sv`
- **[math_addsub](math_addsub.md)** - Combined adder/subtractor
  - Includes: `math_addsub_full_nbit.sv`

#### Subtraction
- **[math_subtractor](math_subtractor.md)** - Subtractor family (single-bit and multi-bit)
  - Includes: `math_subtractor_full.sv`, `math_subtractor_half.sv`, `math_subtractor_full_nbit.sv`, `math_subtractor_ripple_carry.sv`, `math_subtractor_carry_lookahead.sv`

#### Multiplication
- **[math_multiplier_wallace_tree](math_multiplier_wallace_tree.md)** - Wallace tree multiplier family (8/16/32-bit)
  - Includes: `math_multiplier_wallace_tree_008.sv`, `math_multiplier_wallace_tree_016.sv`, `math_multiplier_wallace_tree_032.sv`
  - CSA variants: `math_multiplier_wallace_tree_csa_008.sv`, `math_multiplier_wallace_tree_csa_016.sv`, `math_multiplier_wallace_tree_csa_032.sv`
- **[math_multiplier_dadda_tree](math_multiplier_dadda_tree.md)** - Dadda tree multiplier family (8/16/32-bit)
  - Includes: `math_multiplier_dadda_tree_008.sv`, `math_multiplier_dadda_tree_016.sv`, `math_multiplier_dadda_tree_032.sv`
- **[math_multiplier_dadda_4to2](math_multiplier_dadda_4to2.md)** - Dadda tree multiplier with 4:2 compressors (8-bit for BF16)
  - Includes: `math_multiplier_dadda_4to2_008.sv`
  - Building blocks: `math_compressor_4to2.sv`
- **[math_multiplier_basic](math_multiplier_basic.md)** - Basic multiplier components
  - Includes: `math_multiplier_basic_cell.sv`, `math_multiplier_carry_save.sv`

#### BF16 Floating-Point Arithmetic
- **[math_bf16_adder](math_bf16_adder.md)** - Pipelined BF16 adder with configurable latency
  - Includes: `math_bf16_adder.sv`
  - Dependencies: `shifter_barrel.sv`, `count_leading_zeros.sv`
- **[math_bf16_multiplier](math_bf16_multiplier.md)** - Complete BF16 multiplier with IEEE 754 compliance
  - Includes: `math_bf16_multiplier.sv`
  - Sub-modules: `math_bf16_mantissa_mult.sv`, `math_bf16_exponent_adder.sv`
- **[math_bf16_mantissa_mult](math_bf16_mantissa_mult.md)** - BF16 mantissa multiplier with normalization detection
  - Includes: `math_bf16_mantissa_mult.sv`
- **[math_bf16_exponent_adder](math_bf16_exponent_adder.md)** - BF16 exponent computation with overflow/underflow detection
  - Includes: `math_bf16_exponent_adder.sv`
- **[math_bf16_fma](math_bf16_fma.md)** - BF16 Fused Multiply-Add with FP32 accumulator for AI training
  - Includes: `math_bf16_fma.sv`

#### Compressors and Prefix Cells
- **[math_compressor_4to2](math_compressor_4to2.md)** - 4:2 compressor for fast parallel reduction
  - Includes: `math_compressor_4to2.sv`
- **[math_prefix_cell](math_prefix_cell.md)** - Black cell for parallel prefix adders
  - Includes: `math_prefix_cell.sv`
- **[math_prefix_cell_gray](math_prefix_cell_gray.md)** - Gray cell for parallel prefix adders (area-optimized)
  - Includes: `math_prefix_cell_gray.sv`

### Data Integrity and Error Correction

#### Checksums and CRC
- **[dataint_checksum](dataint_checksum.md)** - Configurable checksum computation
- **[dataint_crc](dataint_crc.md)** - Generic CRC calculation engine
- **[dataint_crc_xor_shift](dataint_crc_xor_shift.md)** - XOR-shift based CRC implementation
- **[dataint_crc_xor_shift_cascade](dataint_crc_xor_shift_cascade.md)** - Cascaded XOR-shift CRC

#### Error Correction
- **[dataint_ecc_hamming_encode_secded](dataint_ecc_hamming_encode_secded.md)** - Hamming ECC encoder with SECDED
- **[dataint_ecc_hamming_decode_secded](dataint_ecc_hamming_decode_secded.md)** - Hamming ECC decoder with SECDED
- **[dataint_parity](dataint_parity.md)** - Parity generation and checking

### Arbitration and Control

#### Arbiters
- **[arbiter_round_robin_simple](arbiter_round_robin_simple.md)** - Simple round-robin arbiter with rotation
- **[arbiter_round_robin](arbiter_round_robin.md)** - Advanced round-robin arbiter
- **[arbiter_round_robin_weighted](arbiter_round_robin_weighted.md)** - Weighted round-robin arbiter
- **[arbiter_priority_encoder](arbiter_priority_encoder.md)** - Priority-based arbiter

### Clock and Reset Management

#### Clock Control
- **[icg](icg.md)** - Integrated Clock Gating cell for power optimization
- **[clock_divider](clock_divider.md)** - Configurable clock frequency divider
- **[clock_gate_ctrl](clock_gate_ctrl.md)** - Advanced clock gating controller
- **[clock_pulse](clock_pulse.md)** - Clock pulse generation and control

#### Reset and Synchronization
- **[reset_sync](reset_sync.md)** - Synchronous reset generation
- **[glitch_free_n_dff_arn](glitch_free_n_dff_arn.md)** - Glitch-free N-bit D flip-flop with async reset
- **[sync_pulse](sync_pulse.md)** - Pulse synchronizer for clock domain crossing
- **[debounce](debounce.md)** - Input signal debouncing

### Counters and Sequences

#### Basic Counters
- **[counter](counter.md)** - Basic parameterizable counter
- **[counter_bin](counter_bin.md)** - Binary counter with enable/reset
- **[counter_johnson](counter_johnson.md)** - Johnson counter (twisted ring)
- **[counter_ring](counter_ring.md)** - Ring counter implementation
- **[counter_freq_invariant](counter_freq_invariant.md)** - Frequency-invariant counter

#### Specialized Counters
- **[counter_bingray](counter_bingray.md)** - Binary to Gray counter
- **[counter_bin_load](counter_bin_load.md)** - Binary counter with load capability
- **[counter_load_clear](counter_load_clear.md)** - Counter with load and clear

### Data Conversion and Encoding

#### Binary Conversions
- **[bin2gray](bin2gray.md)** - Binary to Gray code converter
- **[gray2bin](gray2bin.md)** - Gray to binary code converter
- **[grayj2bin](grayj2bin.md)** - Johnson Gray to binary converter
- **[bin_to_bcd](bin_to_bcd.md)** - Binary to BCD converter

#### Display and Encoding
- **[hex_to_7seg](hex_to_7seg.md)** - Hexadecimal to 7-segment display decoder
- **[encoder](encoder.md)** - Priority encoder
- **[encoder_priority_enable](encoder_priority_enable.md)** - Priority encoder with enable
- **[decoder](decoder.md)** - Binary decoder

### Bit Manipulation and Searching

#### Bit Operations
- **[leading_one_trailing_one](leading_one_trailing_one.md)** - Leading/trailing one detection
- **[count_leading_zeros](count_leading_zeros.md)** - Count leading zeros
- **[find_first_set](find_first_set.md)** - Find first set bit
- **[find_last_set](find_last_set.md)** - Find last set bit
- **[reverse_vector](reverse_vector.md)** - Bit vector reversal

### Shift Operations and LFSRs

#### Shifters
- **[shifter_barrel](shifter_barrel.md)** - Barrel shifter for rotation and shifting
- **[shifter_universal](shifter_universal.md)** - Universal shifter (left/right, logical/arithmetic)

#### Linear Feedback Shift Registers
- **[shifter_lfsr](shifter_lfsr.md)** - Basic Linear Feedback Shift Register
- **[shifter_lfsr_fibonacci](shifter_lfsr_fibonacci.md)** - Fibonacci LFSR implementation
- **[shifter_lfsr_galois](shifter_lfsr_galois.md)** - Galois LFSR implementation

### Memory and Storage

#### FIFO Implementations
- **[fifo_sync](fifo_sync.md)** - Synchronous FIFO with configurable depth
- **[fifo_async](fifo_async.md)** - Asynchronous FIFO for clock domain crossing
- **[fifo_async_div2](fifo_async_div2.md)** - Asynchronous FIFO optimized for divide-by-2 clocks
- **[fifo_control](fifo_control.md)** - FIFO control logic

#### Content Addressable Memory
- **[cam_tag](cam_tag.md)** - Content Addressable Memory for tag matching

### Utility and Miscellaneous

#### Signal Processing
- **[pwm](pwm.md)** - Pulse Width Modulation generator
- **[sort](sort.md)** - Hardware sorting implementation

## Quick Reference

### Module Count by Category
- **Arithmetic Operations**: 25+ modules
- **Data Integrity**: 6 modules
- **Clock/Reset Control**: 4 modules
- **Counters**: 6 modules
- **Converters/Encoders**: 8 modules
- **Bit Manipulation**: 5 modules
- **Shifters/LFSRs**: 4 modules
- **Memory/Storage**: 4 modules
- **Utilities**: 2 modules

### Usage Guidelines

1. **Performance Critical**: Use parallel prefix adders (Brent-Kung, Kogge-Stone) for high-speed arithmetic
2. **Area Constrained**: Use ripple carry implementations for low area requirements
3. **Power Sensitive**: Utilize clock gating (ICG) and frequency-invariant designs
4. **Data Integrity**: Apply ECC and CRC modules for reliable data storage/transmission

### Module Naming Convention

- **math_**: Mathematical/arithmetic operations
- **dataint_**: Data integrity (CRC, ECC, parity, checksum)
- **arbiter_**: Arbitration logic
- **counter_**: Counter implementations
- **shifter_**: Shift operations and LFSRs
- **fifo_**: FIFO memory implementations
- **clock_**: Clock management functions

## Integration Examples

### Building a Simple ALU
```systemverilog
// Use multiple math modules for ALU operations
math_adder_full_nbit #(.N(32)) u_add (.a(op_a), .b(op_b), .cin(1'b0), .sum(alu_sum), .cout(alu_cout));
math_subtractor_full_nbit #(.N(32)) u_sub (.a(op_a), .b(op_b), .bin(1'b0), .diff(alu_diff), .bout(alu_bout));
```

### Clock Domain Crossing
```systemverilog
// Combine async FIFO with reset synchronization
fifo_async #(.DATA_WIDTH(32), .ADDR_WIDTH(4)) u_fifo (.wr_clk(clk_a), .rd_clk(clk_b), ...);
reset_sync u_sync_a (.clk(clk_a), .rst_n_in(global_rst_n), .rst_n_out(rst_sync_a));
reset_sync u_sync_b (.clk(clk_b), .rst_n_in(global_rst_n), .rst_n_out(rst_sync_b));
```

### Data Protection
```systemverilog
// Add ECC protection to memory interface
dataint_ecc_hamming_encode_secded #(.DATA_WIDTH(64)) u_encode (.data_in(mem_data), .ecc_out(mem_ecc));
dataint_ecc_hamming_decode_secded #(.DATA_WIDTH(64)) u_decode (.data_in(mem_data), .ecc_in(mem_ecc), .data_out(corrected_data), .error_detected(ecc_error));
```

## Navigation
- **[Back to RTL Documentation](../index.md)** - Return to main RTL documentation index