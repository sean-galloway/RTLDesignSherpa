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

# rtl-common Modules Index

This directory documents the common RTL module library — the fundamental building blocks for digital design: data integrity, control logic, clock and reset handling, counters, shifters, and the specialized utilities every project ends up needing. Arithmetic lived here too, once — it has its own book now, as the first category below explains.

## Overview

- **[Overview](overview.md)** - Complete overview of the rtl-common library architecture and design philosophy
- **[Quick Start Guide](quickstart.md)** - Browse, integrate, common use cases, pitfalls, and commands

## Module Categories

### Arithmetic and Math Operations

The `math_*` library has its own book now: **[rtl-math](../rtl-math/index.md)**.
The RTL moved to `rtl/math/` and the tests to `val/math/`; the docs followed, so
the three agree.

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
- **[arbiter_round_robin_weighted](arbiter_round_robin_weighted.md)** - Weighted round-robin arbiter (grant-count shares)
- **[arbiter_deficit_round_robin](arbiter_deficit_round_robin.md)** - Deficit round-robin arbiter (cost-proportional shares)
- **[arbiter_token_bucket](arbiter_token_bucket.md)** - Token-bucket request shaper (rate limiting in front of any arbiter)
- **[arbiter_single_client](arbiter_single_client.md)** - Degenerate single-client arbiter (registered ack-held grant)
- **[arbiter_priority_encoder](arbiter_priority_encoder.md)** - Priority-based arbiter

### Clock and Reset Management

#### Clock Control
- **[icg](icg.md)** - Integrated Clock Gating cell for power optimization
- **[clock_divider](clock_divider.md)** - Configurable clock frequency divider
- **[clock_gate_ctrl](clock_gate_ctrl.md)** - Advanced clock gating controller
- **[clock_pulse](clock_pulse.md)** - Clock pulse generation and control

#### Reset and Synchronization
- **[reset_sync](reset_sync.md)** - Synchronous reset generation
<!-- glitch_free_n_dff_arn and sync_pulse moved to rtl/cdc (2026-08-08):
     see docs/markdown/rtl-cdc/ -->
- **[debounce](debounce.md)** - Input signal debouncing

### Counters and Sequences

#### Basic Counters
- **[counter](counter.md)** - Basic parameterizable counter
- **[counter_bin](counter_bin.md)** - Binary counter with enable/reset
- **[counter_ring](counter_ring.md)** - Ring counter implementation
- **[counter_freq_invariant](counter_freq_invariant.md)** - Frequency-invariant counter

#### Specialized Counters
- **[counter_bin_load](counter_bin_load.md)** - Binary counter with load capability
- **[counter_load_clear](counter_load_clear.md)** - Counter with load and clear

### Data Conversion and Encoding

#### Binary Conversions
- **[bin_to_bcd](bin_to_bcd.md)** - Binary to BCD converter

> Gray/Johnson conversion (`bin2gray`, `gray2bin`, `johnson2bin`) and the
> Gray/Johnson counters (`counter_bingray`, `counter_johnson`) moved to
> `rtl/cdc/` with the rest of the clock-crossing set.

#### Display and Encoding
- **[hex_to_7seg](hex_to_7seg.md)** - Hexadecimal to 7-segment display decoder
- **[encoder](encoder.md)** - Priority encoder
- **[encoder_priority_enable](encoder_priority_enable.md)** - Priority encoder with enable
- **[decoder](decoder.md)** - Binary decoder

### Bit Manipulation and Searching

#### Bit Operations
- **[leading_one_trailing_one](leading_one_trailing_one.md)** - Leading/trailing one detection
- **[count_leading_zeros](count_leading_zeros.md)** - Count leading zeros (scan from MSB down)
- **[count_trailing_zeros](count_trailing_zeros.md)** - Count trailing zeros (scan from LSB up)
- **[find_first_set](find_first_set.md)** - Find first set bit
- **[find_last_set](find_last_set.md)** - Find last set bit
- **[reverse_vector](reverse_vector.md)** - Bit vector reversal

### Shift Operations and LFSRs

#### Shifters
- **[shifter_barrel](shifter_barrel.md)** - Barrel shifter for rotation and shifting
- **[shifter_universal](shifter_universal.md)** - Universal shifter (left/right, logical/arithmetic)
- **[shifter_beat_pack](shifter_beat_pack.md)** - Bit-granular beat-packing shifter (runtime beat width)

#### Linear Feedback Shift Registers
- **[shifter_lfsr](shifter_lfsr.md)** - Basic Linear Feedback Shift Register
- **[shifter_lfsr_fibonacci](shifter_lfsr_fibonacci.md)** - Fibonacci LFSR implementation
- **[shifter_lfsr_galois](shifter_lfsr_galois.md)** - Galois LFSR implementation

### Memory and Storage

#### FIFO Implementations
- **[fifo_sync](fifo_sync.md)** - Synchronous FIFO with configurable depth

`fifo_async` moved to `rtl/cdc/`. Two more wrappers are documented here but
lived in `rtl/integ_common/` — integration examples rather than library
modules. That area was retired in `01d1c3e6` along with `rtl/integ_amba/`;
the wrappers are recoverable from git history if the pattern is wanted again.
- **[fifo_control](fifo_control.md)** - FIFO control logic

#### Content Addressable Memory
- **[cam_tag](cam_tag.md)** - Content Addressable Memory for tag matching

### Utility and Miscellaneous

#### Signal Processing
- **[pwm](pwm.md)** - Pulse Width Modulation generator
- **[sort](sort.md)** - Hardware sorting implementation
<!-- mod_3_compress moved to rtl/math as math_mod_3_compress (2026-08-08);
     see docs/markdown/rtl-math/math_mod_3_compress.md -->

## Quick Reference

### Module Count by Category

**48 modules** in `rtl/common/`. Two sets have moved out, and they're counted in
their own books, not here:

- Arithmetic (`math_*`) split out to `rtl/math/` — see [rtl-math](../rtl-math/index.md).
- Clock-domain-crossing modules moved to `rtl/cdc/` — `bin2gray`, `gray2bin`,
  `johnson2bin`, `counter_bingray`, `counter_johnson` and `fifo_async` live
  there now, alongside `cdc_synchronizer` and the handshake modules.

| Category | Count |
|---|---|
| Clock, Reset & Debounce | 6 |
| Data Integrity | 7 |
| Counters | 6 |
| Bit Ops & Search | 6 |
| Shifters & LFSRs | 6 |
| Arbiters | 7 |
| Conversion & Encoding | 5 |
| Miscellaneous | 2 |
| FIFOs | 2 |
| CAM | 1 |

The counts come from `ls rtl/common/*.sv` — regenerate them rather than
hand-editing. They sum to 48, and every module in the tree falls into exactly
one row.

### Usage Guidelines

1. **Arithmetic**: adders, multipliers and dividers aren't in this library
   anymore — they moved to `rtl/math/`. For the speed/area trade-off between
   parallel-prefix (Brent-Kung, Han-Carlson) and ripple-carry implementations,
   see the [rtl-math](../rtl-math/index.md) book.
2. **Area Constrained**: prefer the simpler variant where one exists (for
   example `arbiter_round_robin_simple` over the weighted arbiter).
3. **Power Sensitive**: use clock gating (ICG) and frequency-invariant designs.
4. **Data Integrity**: apply the ECC and CRC modules for reliable data storage/transmission.

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
math_adder_full_nbit #(.N(32)) u_add (.i_a(op_a), .i_b(op_b), .i_c(1'b0), .ow_sum(alu_sum), .ow_carry(alu_cout));
math_subtractor_full_nbit #(.N(32)) u_sub (.i_a(op_a), .i_b(op_b), .i_b_in(1'b0), .ow_d(alu_diff), .ow_b(alu_bout));
```

### Clock Domain Crossing
```systemverilog
// Combine async FIFO with reset synchronization
// fifo_async now lives in rtl/cdc/ -- see the rtl-cdc book
fifo_async #(.DATA_WIDTH(32), .DEPTH(16)) u_fifo (.wr_clk(clk_a), .rd_clk(clk_b), ...);
reset_sync u_sync_a (.clk(clk_a), .rst_n(global_rst_n), .sync_rst_n(rst_sync_a));
reset_sync u_sync_b (.clk(clk_b), .rst_n(global_rst_n), .sync_rst_n(rst_sync_b));
```

### Data Protection
```systemverilog
// Add ECC protection to memory interface.
// The parameter is WIDTH (not DATA_WIDTH), the encoder emits a single combined
// codeword (data + parity) on encoded_data, and the decoder is CLOCKED.
dataint_ecc_hamming_encode_secded #(.WIDTH(64)) u_encode (
    .data         (mem_data),
    .encoded_data (mem_codeword)      // WIDTH + ParityBits + 1 bits
);

dataint_ecc_hamming_decode_secded #(.WIDTH(64)) u_decode (
    .clk                   (clk),
    .rst_n                 (rst_n),
    .enable                (1'b1),
    .hamming_data          (mem_codeword),
    .data                  (corrected_data),
    .error_detected        (ecc_single_error),
    .double_error_detected (ecc_double_error)
);
```

## Navigation
- **[Back to RTL Documentation](../index.md)** - Return to main RTL documentation index
