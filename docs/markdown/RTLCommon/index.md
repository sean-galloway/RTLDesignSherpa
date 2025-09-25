# RTLCommon Modules Index

This directory contains documentation for the common RTL modules library, providing fundamental building blocks for digital design including arithmetic operations, data integrity functions, control logic, and specialized utilities.

## Overview

- **[Overview](overview.md)** - Complete overview of the RTLCommon library architecture and design philosophy

## Module Categories

### Arithmetic and Math Operations

#### Basic Arithmetic
- **[math_adder_full](math_adder_full.md)** - Single-bit full adder with carry-in/carry-out
- **[math_adder_half](math_adder_half.md)** - Single-bit half adder (2-input)
- **[math_adder_ripple_carry](math_adder_ripple_carry.md)** - Multi-bit ripple carry adder
- **[math_adder_carry_lookahead](math_adder_carry_lookahead.md)** - Fast carry lookahead adder
- **[math_adder_carry_save](math_adder_carry_save.md)** - Carry-save adder for multiple operands
- **[math_adder_kogge_stone_nbit](math_adder_kogge_stone_nbit.md)** - High-speed Kogge-Stone parallel prefix adder

#### Advanced Adders
- **[math_adder_brent_kung_008](math_adder_brent_kung_008.md)** - 8-bit Brent-Kung parallel prefix adder
- **[math_adder_brent_kung_016](math_adder_brent_kung_016.md)** - 16-bit Brent-Kung parallel prefix adder
- **[math_adder_brent_kung_032](math_adder_brent_kung_032.md)** - 32-bit Brent-Kung parallel prefix adder
- **[math_addsub_full_nbit](math_addsub_full_nbit.md)** - Combined N-bit adder/subtractor

#### Subtraction
- **[math_subtractor_full](math_subtractor_full.md)** - Single-bit full subtractor
- **[math_subtractor_half](math_subtractor_half.md)** - Single-bit half subtractor
- **[math_subtractor_ripple_carry](math_subtractor_ripple_carry.md)** - Multi-bit ripple carry subtractor

#### Multiplication
- **[math_multiplier_wallace_tree_008](math_multiplier_wallace_tree_008.md)** - 8-bit Wallace tree multiplier
- **[math_multiplier_wallace_tree_016](math_multiplier_wallace_tree_016.md)** - 16-bit Wallace tree multiplier
- **[math_multiplier_wallace_tree_032](math_multiplier_wallace_tree_032.md)** - 32-bit Wallace tree multiplier
- **[math_multiplier_dadda_tree_008](math_multiplier_dadda_tree_008.md)** - 8-bit Dadda tree multiplier
- **[math_multiplier_dadda_tree_016](math_multiplier_dadda_tree_016.md)** - 16-bit Dadda tree multiplier
- **[math_multiplier_dadda_tree_032](math_multiplier_dadda_tree_032.md)** - 32-bit Dadda tree multiplier

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