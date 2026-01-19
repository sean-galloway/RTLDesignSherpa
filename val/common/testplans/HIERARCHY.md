# RTL Common Module Hierarchy

## Overview

This document defines the dependency hierarchy for rtl/common modules.
Testing proceeds bottom-up: achieve 95%+ on lower levels before moving up.

## Level 0: Primitives (No Dependencies)

These are the fundamental building blocks with no internal module instantiations.

### Math Primitives
| Module | Description | Test File |
|--------|-------------|-----------|
| math_adder_half.sv | 1-bit half adder (XOR, AND) | test_math_adder_half.py |
| math_adder_full.sv | 1-bit full adder with carry | test_math_adder_full.py |
| math_subtractor_half.sv | 1-bit half subtractor | test_math_subtractor_half.py |
| math_subtractor_full.sv | 1-bit full subtractor | test_math_subtractor_full.py |
| math_adder_carry_save.sv | Single CSA cell | test_math_adder_carry_save.py |
| math_multiplier_basic_cell.sv | Single multiplier cell | (none) |

### Encoders/Decoders
| Module | Description | Test File |
|--------|-------------|-----------|
| encoder.sv | N-to-log2(N) encoder | test_encoder.py |
| decoder.sv | log2(N)-to-N decoder | test_decoder.py |
| encoder_priority_enable.sv | Priority encoder with enable | test_encoder_priority_enable.py |

### Code Converters
| Module | Description | Test File |
|--------|-------------|-----------|
| bin2gray.sv | Binary to Gray code | test_bin2gray.py |
| gray2bin.sv | Gray code to binary | test_gray2bin.py |
| bin_to_bcd.sv | Binary to BCD | test_bin_to_bcd.py |

### Simple Counters
| Module | Description | Test File |
|--------|-------------|-----------|
| counter_ring.sv | Ring counter (one-hot) | test_counter_ring.py |
| counter_johnson.sv | Johnson counter (twisted ring) | test_counter_johnson.py |

### Clock Utilities
| Module | Description | Test File |
|--------|-------------|-----------|
| clock_divider.sv | Clock frequency divider | test_clock_divider.py |
| clock_gate_ctrl.sv | Clock gating control | test_clock_gate_ctrl.py |
| clock_pulse.sv | Clock pulse generator | test_clock_pulse.py |

### Data Integrity
| Module | Description | Test File |
|--------|-------------|-----------|
| dataint_parity.sv | Parity generator/checker | test_dataint_parity.py |
| dataint_checksum.sv | Checksum calculator | test_dataint_checksum.py |

---

## Level 1: Basic Building Blocks (Use Level 0)

These modules instantiate Level 0 primitives.

### N-bit Adders/Subtractors
| Module | Uses | Test File |
|--------|------|-----------|
| math_adder_full_nbit.sv | math_adder_full | test_math_adder_full_nbit.py |
| math_adder_ripple_carry.sv | math_adder_full | test_math_adder_ripple_carry.py |
| math_subtractor_full_nbit.sv | math_subtractor_full | test_math_subtractor_full_nbit.py |
| math_subtractor_ripple_carry.sv | math_subtractor_full | test_math_subtractor_ripple_carry.py |
| math_adder_carry_save_nbit.sv | math_adder_carry_save | test_math_adder_carry_save_nbit.py |

### Binary Counters
| Module | Uses | Test File |
|--------|------|-----------|
| counter_bin.sv | (internal logic) | test_counter_bin.py |
| counter_bin_load.sv | counter_bin | test_counter_bin_load.py |
| counter_load_clear.sv | (internal logic) | test_counter_load_clear.py |

### Data Integrity (Complex)
| Module | Uses | Test File |
|--------|------|-----------|
| dataint_crc_xor_shift.sv | (internal logic) | test_dataint_crc.py |
| dataint_ecc_hamming_encode_secded.sv | (internal logic) | test_dataint_ecc_hamming_secded.py |
| dataint_ecc_hamming_decode_secded.sv | (internal logic) | test_dataint_ecc_hamming_secded.py |

---

## Level 2: Compound Modules (Use Level 1)

### Advanced Adders
| Module | Uses | Test File |
|--------|------|-----------|
| math_adder_carry_lookahead.sv | math_adder_full | test_math_adder_carry_lookahead.py |
| math_adder_brent_kung_*.sv | BK primitives | test_math_adder_brent_kung.py |
| math_adder_han_carlson_*.sv | HC primitives | test_math_adder_han_carlson.py |
| math_adder_kogge_stone_nbit.sv | KS primitives | test_math_adder_kogge_stone_nbit.py |

### Multipliers
| Module | Uses | Test File |
|--------|------|-----------|
| math_multiplier_dadda_*.sv | adders, compressors | test_math_multiplier_dadda.py |
| math_multiplier_wallace_*.sv | adders, CSA | test_math_multiplier_wallace.py |
| math_multiplier_carry_save.sv | CSA cells | test_math_multiplier_carry_save.py |

### Gray Code Counter
| Module | Uses | Test File |
|--------|------|-----------|
| counter_bingray.sv | bin2gray | test_counter_bingray.py |
| counter_freq_invariant.sv | counter_bin | test_counter_freq_invariant.py |

### FIFO Control
| Module | Uses | Test File |
|--------|------|-----------|
| fifo_control.sv | counter_bin | test_fifo_buffer.py |

---

## Level 3: Integration Modules (Use Level 2)

### FIFOs
| Module | Uses | Test File |
|--------|------|-----------|
| fifo_sync.sv | fifo_control | test_fifo_buffer.py |
| fifo_async.sv | fifo_control, counter_bingray, sync | test_fifo_buffer_async.py |
| fifo_async_div2.sv | fifo_control, counter_johnson | test_fifo_buffer_async_div2.py |

### Arbiters
| Module | Uses | Test File |
|--------|------|-----------|
| arbiter_priority_encoder.sv | encoder | test_arbiter_priority_encoder.py |
| arbiter_round_robin_simple.sv | (internal logic) | test_arbiter_round_robin_simple.py |
| arbiter_round_robin.sv | arbiter_priority_encoder | test_arbiter_round_robin.py |
| arbiter_round_robin_weighted.sv | arbiter_round_robin | test_arbiter_round_robin_weighted.py |

### Data Integrity (Integration)
| Module | Uses | Test File |
|--------|------|-----------|
| dataint_crc.sv | crc_xor_shift_cascade | test_dataint_crc.py |
| dataint_ecc.sv | encode + decode | test_dataint_ecc.py |

---

## Coverage Strategy

### Phase 1: Level 0 (Target: 95%+)
1. Run all primitive tests with COVERAGE=1
2. Analyze gaps, add targeted tests
3. Verify 95%+ before proceeding

### Phase 2: Level 1 (Target: 95%+)
1. Run Level 1 tests with COVERAGE=1
2. Level 0 coverage from Level 1 tests counts toward Level 0
3. Analyze gaps, add targeted tests

### Phase 3: Level 2-3 (Target: 95%+)
1. Run compound module tests
2. Coverage accumulates from all levels
3. Focus on integration-specific paths

### Commands

```bash
# Run Level 0 tests
COVERAGE=1 REG_LEVEL=FUNC pytest test_math_adder_half.py test_math_adder_full.py \
  test_encoder.py test_decoder.py test_bin2gray.py test_counter_ring.py -v

# Run Level 1 tests
COVERAGE=1 REG_LEVEL=FUNC pytest test_math_adder_full_nbit.py test_counter_bin.py -v

# Run all levels and merge coverage
COVERAGE=1 REG_LEVEL=FULL pytest val/common/ -v
```
