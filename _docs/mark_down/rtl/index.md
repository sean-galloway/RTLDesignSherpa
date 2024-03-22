---
title: RTL List
date: 2024-03-15
type: index
layout: docs
categories: ["RTL", "RTL List"]
---

# Grouped by Similar Functionality

In most cases, I don't list all the items' sub-blocks. These are listed on their page if needed. I list sub-blocks if there is a solid reason to show what is happening under the hood. The sub-blocks are listed with items that instantiate them and with a usage explained. Some logic is generated in my scripts, and 008/016/032 versions are available. I only describe the 008 version as they are all really the same. Where the code is not entirely original, I have a copy of the source code in \$REPO_ROOT/rtl/common/Original_Source_Files_For_Reference/

Note: I have usually made significant changes, primarily for performance reasons.

## Simple to Complex List

1\. Adders and Subtractors, simple

- [math_adder_half](math_adder_half)

- [math_subtractor_half](math_subtractor_half)

- [math_adder_full](math_adder_full)

- [math_subtractor_full](math_subtractor_full)

- [math_adder_ripple_carry](math_adder_ripple_carry)

- [math_subtractor_ripple_carry](math_subtractor_ripple_carry)

- [math_adder_carry_lookahead](math_adder_carry_lookahead)

- [math_subtractor_carry_lookahead](math_subtractor_carry_lookahead)

2\. Arithmetic and Logic Modules

- [math_adder_carry_save](math_adder_carry_save)

- [math_adder_carry_save_nbit](math_adder_carry_save_nbit)

- [math_adder_full_nbit](math_adder_full_nbit)

- [math_addsub_full_nbit](math_addsub_full_nbit)

- [math_adder_hierarchical](math_adder_hierarchical)

- [math_subtractor_full_nbit](math_subtractor_full_nbit)

3\. Brent-Kung Adder Series

- [math_adder_brent_kung_008](math_adder_brent_kung_008)

- [math_adder_brent_kung_bitwisepg](math_adder_brent_kung_bitwisepg)

- [math_adder_brent_kung_pg](math_adder_brent_kung_pg)

- [math_adder_brent_kung_grouppg_008](math_adder_brent_kung_grouppg_008)

- [math_adder_brent_kung_black](math_adder_brent_kung_black)

- [math_adder_brent_kung_gray](math_adder_brent_kung_gray)

- [math_adder_brent_kung_sum](math_adder_brent_kung_sum)

4\. Kogge-Stone Adder

- [math_adder_kogge_stone_nbit](math_adder_kogge_stone_nbit)

5\. Multipliers

- [math_multiplier_array](math_multiplier_array)

- [math_multiplier_carry_lookahead](math_multiplier_carry_lookahead)

- [Math Multiplier Booth's](math_multiplier_booths)

- [math_multiplier_wallace_tree_csa_008](math_multiplier_wallace_tree_csa_008)

- [math_multiplier_dadda_tree_008](math_multiplier_dadda_tree_008)

- [math_multiplier_wallace_tree_008](math_multiplier_wallace_tree_008)

6\. Dividers

- [Math Divider SRT](math_divider_srt)

7\. Encoder and Decoders

- [decoder](decoder)

- [encoder](encoder)

- [encoder_priority_enable](encoder_priority_enable)

- [hex_to_7seg](hex_to_7seg)

- [Binary to BCD](bin_to_bcd)

- [gray2bin](bin2gray)

- [gray2bin](gray2bin)

- [grayj2bin](grayj2bin)

- [math_multiplier_booth_radix_4_encoder](math_multiplier_booth_radix_4_encoder)

- [math_booth_encoding](math_booth_encoding)

8\. Glitch and Synchronization

- [glitch_free_n_dff_arn](glitch_free_n_dff_arn)

- [Reset Synchronizer](reset_sync)

9\. Set Finders

- [count leading zeros](count_leading_zeros)

- [leading_one_trailing_one](leading_one_trailing_one)

  Sub-Blocks

  - [find_last_set](find_last_set)

  - [find_first_set](find_first_set)

10\. Counters

- [counter](counter)

- [counter load/clear](counter_load_clear)

- [counter_bin](counter_bin)

- [counter_johnson](counter_johnson)

- [counter_bingray](counter_bingray)

- [counter_ring](counter_ring)

11\. Sorting and Reversing

- [sort](sort)

- [reverse_vector](reverse_vector)

12\. Shift Registers

- [shifter_barrel](shifter_barrel)

- [shifter_lfsr](shifter_lfsr)

- [shifter_lfsr_fibonacci](shifter_lfsr_fibonacci)

- [shifter_lfsr_galois](shifter_lfsr_galois)

- [Shifter_Universal](shifter_universal)

13\. Debounce Circuit

- [debounce](debounce)

14\. Clock and Pulse Generators

- [clock_divider](clock_divider)

- [clock_pulse](clock_pulse)

- [PWM](pwm)

15\. Arbiters

- [arbiter_round_robin](arbiter_round_robin)

- [arbiter_weighted_round_robin](arbiter_weighted_round_robin)

- [arbiter_round_robin_subinst](arbiter_round_robin_subinst)

- [arbiter_fixed_priority](arbiter_fixed_priority)

16\. FIFOs

- [Synchronous](fifo_sync)

- [Asynchronous](fifo_async)

- [Asynchronous div by 2](fifo_async_div2)

  Sub-Blocks

  - [Binary Counter](counter_bin)

  - [Binary and Gray Counter](counter_bingray)

  - [Johnson Counter](counter_johnson)

  - [FIFO Control, for empty/full, used for sync and async blocks](fifo_control)

  - [Gray to Binary](gray2bin)

  - [Johnson to Binary](grayj2bin)

17\. Data Integrity

- [Parity](dataint_parity)

- [Checksum](dataint_checksum)

- [CRC](dataint_crc)

  Sub-Blocks

  - [CRC XOR Cascade](dataint_crc_xor_shift_cascade)

  - [CRC XOR Shift](dataint_crc_xor_shift)

- [Hamming ECC Encode](dataint_ecc_hamming_encode_secded)

- [Hamming ECC Decode](dataint_ecc_hamming_decode_secded)

---

[Back to Main Index](/)

---
