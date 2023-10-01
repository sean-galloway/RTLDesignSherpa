# File List

These are some random but valuable sets of essential Verilog functions. The file naming convention is artificial and probably not used in the industry. I like to find all of the arbiters or multipliers easily, for example. There is a directory called Original_Source_Files_For_Reference/. In some cases, I based the eventual code off of something somewhere on the internet. I have tried in all cases to cite the source. I also have the original source in this directory. In all cases, I made significant changes to the source material. Usually, to parameterize the code, but often to fix performance issues.

## Arbiters

    arbiter_fixed_priority.sv 
    arbiter_round_robin_subinst.sv
    arbiter_round_robin.sv -- a good, simple round robin arbiter.
    arbiter_weighted_round_robin.sv -- This is the most generic arbiter to use. The weights can be set to the same values if one wants strictly round-robin behavior.

## Fifos and Support Logic

    bin2gray.sv -- binary to gray converter (not used, eventually)
    counter_bingray.sv -- a counter that outputs a binary value and a gray value
    counter_bin.sv -- a simple parameterized binary counter
    counter_johnson.sv -- a Jonhnson counter
    fifo_async_any_even.sv -- a unique implementation, to my knowledge. This async fifo allows the depth to be any even number.
    fifo_async.sv -- a standard parameterized async fifo; only depths that are powers of two are allowed
    fifo_sync.sv -- a standard parameterized fifo
    glitch_free_n_dff_arn.sv
    gray2bin.sv -- a generic gray toe binary converter
    grayj2bin.sv -- a Johnson counter to the binary converter (used in any even FIFO)

## Math Related Functions

I am still determining how useful these will be. I have a set of FPGA experiments planned to test different theories.

    math_adder_brent_kung_008.sv
    math_adder_brent_kung_016.sv
    math_adder_brent_kung_032.sv
    math_adder_brent_kung_bitwisepg.sv
    math_adder_brent_kung_black.sv
    math_adder_brent_kung_gray.sv
    math_adder_brent_kung_grouppg_008.sv
    math_adder_brent_kung_grouppg_016.sv
    math_adder_brent_kung_grouppg_032.sv
    math_adder_brent_kung_pg.sv
    math_adder_brent_kung_sum.sv
    math_adder_carry_lookahead.sv
    math_adder_carry_save_nbit.sv
    math_adder_carry_save.sv
    math_adder_full_nbit.sv
    math_adder_full.sv
    math_adder_half.sv
    math_adder_hierarchical.sv
    math_adder_kogge_stone_nbit.sv
    math_adder_ripple_carry.sv
    math_addsub_full_nbit.sv
    math_booth_encoding.sv
    math_divider_reciprocal.sv
    math_divider_srt.sv
    math_multiplier_array.sv
    math_multiplier_booth_radix_4_encoder.sv
    math_multiplier_booths.sv
    math_multiplier_carry_lookahead.sv
    math_multiplier_dadda_tree_008.sv
    math_multiplier_dadda_tree_016.sv
    math_multiplier_dadda_tree_032.sv
    math_multiplier_wallace_tree_008.sv
    math_multiplier_wallace_tree_016.sv
    math_multiplier_wallace_tree_032.sv
    math_multiplier_wallace_tree_csa_008.sv
    math_multiplier_wallace_tree_csa_016.sv
    math_multiplier_wallace_tree_csa_032.sv
    math_subtractor_carry_lookahead.sv
    math_subtractor_full_nbit.sv
    math_subtractor_full.sv
    math_subtractor_half.sv
    math_subtractor_ripple_carry.sv

## Other Useful Items

These blocks might be used in some of the logic above, but their usefulness could extend beyond that.

    bin_to_bcd.sv -- binary to BCD FSM
    clock_divider.sv -- generic clock divider
    clock_pulse.sv -- generic clock pulse generator
    counter_load_clear.sv -- load/clear counter
    count_leading_zeros.sv -- Icarus doesn't implement the Verilog $clz function, so I had to make this
    debounce.sv -- generic button debounce function
    decoder.sv -- generic decoder
    encoder_priority_enable.sv -- encoder with priority enable
    encoder.sv -- simple encoder
    find_first_set.sv -- finds the first one starting from bit zero and incrementing in a vector
    find_last_set.sv -- finds the last one starting from the last bit and decrementing in a vector
    hex_to_7seg.sv -- takes a single hex value as input, and it generates the controls for a single 7-segment display
    leading_one_trailing_one.sv -- this module takes a vector as input and finds both the leading and trailing one
    pwm.sv -- generic pulse width modulator, with a repeat function
    reverse_vector.sv -- reverses a vector
    shifter_barrel.sv -- fairly generic barrel shifter
    shifter_lfsr.sv -- parameterized LFSR that allows for a seed and choosing the ideal points to pick off in the vector
    shifter_universal.sv -- a fairly generic shift register
    sort.sv -- this module takes in a single long vector that has many numbers in it sorts them, and outputs the sorted vector.
