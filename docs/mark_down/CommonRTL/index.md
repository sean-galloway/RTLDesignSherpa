# Grouped by Similar Functionality

In most cases, I don't list all the items' sub-blocks. These are listed on their page if needed. I list sub-blocks if there is a solid reason to show what is happening under the hood. The sub-blocks are listed with items that instantiate them and with a usage explained. Some logic is generated in my scripts, and 008/016/032 versions are available. I only describe the 008 version as they are all really the same. Where the code is not entirely original, I have a copy of the source code in \$REPO_ROOT/rtl/common/Original_Source_Files_For_Reference/

Note: I have usually made significant changes, primarily for performance reasons.

## Simple to Complex List

1\. Adders and Subtractors, simple

- [math_adder_half](math_adder_half.md)
- [math_subtractor_half](math_subtractor_half.md)
- [math_adder_full](math_adder_full.md)
- [math_subtractor_full](math_subtractor_full.md)
- [math_adder_ripple_carry](math_adder_ripple_carry.md)
- [math_subtractor_ripple_carry](math_subtractor_ripple_carry.md)
- [math_adder_carry_lookahead](math_adder_carry_lookahead.md)
- [math_subtractor_carry_lookahead](math_subtractor_carry_lookahead.md)

2\. Arithmetic and Logic Modules

- [math_adder_carry_save](math_adder_carry_save.md)
- [math_adder_carry_save_nbit](math_adder_carry_save_nbit.md)
- [math_adder_full_nbit](math_adder_full_nbit.md)
- [math_addsub_full_nbit](math_addsub_full_nbit.md)
- [math_subtractor_full_nbit](math_subtractor_full_nbit.md)

3\. Brent-Kung Adder Series

- [math_adder_brent_kung_008](math_adder_brent_kung_008.md)
- [math_adder_brent_kung_bitwisepg](math_adder_brent_kung_bitwisepg.md)
- [math_adder_brent_kung_pg](math_adder_brent_kung_pg.md)
- [math_adder_brent_kung_grouppg_008](math_adder_brent_kung_grouppg_008.md)
- [math_adder_brent_kung_black](math_adder_brent_kung_black.md)
- [math_adder_brent_kung_gray](math_adder_brent_kung_gray.md)
- [math_adder_brent_kung_sum](math_adder_brent_kung_sum.md)

4\. Kogge-Stone Adder

- [math_adder_kogge_stone_nbit](math_adder_kogge_stone_nbit.md)

5\. Multipliers

- [math_multiplier_array](math_multiplier_array.md)
- [math_multiplier_carry_lookahead](math_multiplier_carry_lookahead.md)
- [Math Multiplier Booth's](math_multiplier_booths.md)
- [math_multiplier_wallace_tree_csa_008](math_multiplier_wallace_tree_csa_008.md)
- [math_multiplier_dadda_tree_008](math_multiplier_dadda_tree_008.md)
- [math_multiplier_wallace_tree_008](math_multiplier_wallace_tree_008.md)

6\. Dividers

- [Math Divider SRT](math_divider_srt.md)

7\. Encoder and Decoders

- [decoder](decoder.md)
- [encoder](encoder.md)
- [encoder_priority_enable](encoder_priority_enable.md)
- [hex_to_7seg](hex_to_7seg.md)
- [Binary to BCD](bin_to_bcd.md)
- [gray2bin](bin2gray.md)
- [gray2bin](gray2bin.md)
- [grayj2bin](grayj2bin.md)
- [math_multiplier_booth_radix_4_encoder](math_multiplier_booth_radix_4_encoder.md)
- [math_booth_encoding](math_booth_encoding.md)

8\. Glitch and Synchronization

- [glitch_free_n_dff_arn](glitch_free_n_dff_arn.md)
- [Reset Synchronizer](reset_sync.md)

9\. Set Finders

- [count leading zeros](count_leading_zeros.md)
- [leading_one_trailing_one](leading_one_trailing_one.md)

  Sub-Blocks

  - [find_last_set](find_last_set.md)
  - [find_first_set](find_first_set.md)

10\. Counters

- [counter](counter.md)
- [counter load/clear](counter_load_clear.md)
- [counter_bin](counter_bin.md)
- [counter_johnson](counter_johnson.md)
- [counter_bingray](counter_bingray.md)
- [counter_ring](counter_ring.md)

11\. Sorting and Reversing

- [sort](sort.md)
- [reverse_vector](reverse_vector.md)

12\. Shift Registers

- [shifter_barrel](shifter_barrel.md)
- [shifter_lfsr](shifter_lfsr.md)
- [shifter_lfsr_fibonacci](shifter_lfsr_fibonacci.md)
- [shifter_lfsr_galois](shifter_lfsr_galois.md)
- [Shifter_Universal](shifter_universal.md)

13\. Debounce Circuit

- [debounce](debounce.md)

14\. Clock and Pulse Generators

- [clock_divider](clock_divider.md)
- [clock_pulse](clock_pulse.md)
- [PWM](pwm.md)

15\. Arbiters

- [arbiter_round_robin](arbiter_round_robin.md)
- [arbiter_weighted_round_robin](arbiter_weighted_round_robin.md)
- [arbiter_round_robin_subinst](arbiter_round_robin_subinst.md)
- [arbiter_fixed_priority](arbiter_fixed_priority.md)

16\. FIFOs

- [Synchronous](fifo_sync.md)
- [Asynchronous](fifo_async.md)
- [Asynchronous div by 2](fifo_async_div2.md)

  Sub-Blocks

  - [Binary Counter](counter_bin.md)
  - [Binary and Gray Counter](counter_bingray.md)
  - [Johnson Counter](counter_johnson.md)
  - [FIFO Control, for empty/full, used for sync and async blocks](fifo_control.md)
  - [Gray to Binary](gray2bin.md)
  - [Johnson to Binary](grayj2bin.md)

17\. Data Integrity

- [Parity](dataint_parity.md)
- [Checksum](dataint_checksum.md)
- [CRC](dataint_crc.md)

  Sub-Blocks
  - [CRC XOR Cascade](dataint_crc_xor_shift_cascade.md)
  - [CRC XOR Shift](dataint_crc_xor_shift.md)
- [Hamming ECC Encode](dataint_ecc_hamming_encode_secded.md)
- [Hamming ECC Decode](dataint_ecc_hamming_decode_secded.md)

18\. CAM/Cache

- [Content Addressable Memory](cam_tag.md)
- [Cache Controller with true LRU](cache_lru.md)
- [Cache Controller with PLRU](cache_plru.md)
- [Cache Controller with PLRU and MESI FSM](cache_plru_mesi.md)

---

[Back to Readme](../../../README.md)

---
