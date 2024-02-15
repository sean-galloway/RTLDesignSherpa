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

- [math_adder_hierarchical](math_adder_hierarchical.md)

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

- [encoder](encoder.md)

- [encoder_priority_enable](encoder_priority_enable.md)

- [hex_to_7seg](hex_to_7seg.md)

- [gray2bin](gray2bin.md)

- [grayj2bin](grayj2bin.md)

- [math_multiplier_booth_radix_4_encoder](math_multiplier_booth_radix_4_encoder.md)

- [math_booth_encoding](math_booth_encoding.md)

8\. Glitch and Synchronization

- [glitch_free_n_dff_arn](glitch_free_n_dff_arn.md)

9\. Set Finders

- [find_last_set](find_last_set.md)

- [find_first_set](find_first_set.md)

10\. Counters

- [counter_bin](counter_bin.md)

- [counter_johnson](counter_johnson.md)

- [counter_bingray](counter_bingray.md)

11\. Sorting and Reversing

- [sort](sort.md)

- [reverse_vector](reverse_vector.md)

12\. Shift Registers

- [shifter_barrel](shifter_barrel.md)

- [shifter_lfsr](shifter_lfsr.md)

- [Shifter_Universal](Shifter_Universal.md)

13\. Debounce Circuit

- [debounce](debounce.md)

14\. Clock and Pulse Generators

- [clock_divider](clock_divider.md)

- [clock_pulse](clock_pulse.md)

- [pwm](pwm.md)

15\. Arbiters

- [arbiter_round_robin](arbiter_round_robin.md)

- [arbiter_weighted_round_robin](arbiter_weighted_round_robin.md)

- [arbiter_round_robin_subinst](arbiter_round_robin_subinst.md)

- [arbiter_fixed_priority](arbiter_fixed_priority.md)

---

[Back to Readme](../../../README.md)

----------
