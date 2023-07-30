# File List
These are some fairly random, but somewhat useful set of basic verilog functions.
Arguably, the math related ones aren't useful other than to study.
----------------------------------------------------------------
### Fifo Related Files
* sync_fifo.sv 
* bin2gray.sv 
* gray2bin.sv 
* glitch_free_n_dff_arn.sv 
* async_fifo.sv 

### Arbiters
These are all parameterized.
* round_robin_arbiter.sv 
* weighted_round_robin.sv --> this is a good all around choice, just set the weights to all 1 for a simple round robin 
* fixed_prio_arbiter.sv
* rrb_arb.sv

### Miscellaneous
These are all parameterized.
* barrel_shifter.sv
* bin_to_bcd.sv
* hex_to_7seg.sv
* clock_divider.sv
* clock_pulse.sv
* count_leading_zeros.sv -- the free tools don't seem to support the $clz function
* debounce.sv -- for debouncing buttons and switches
* decoder.sv 
* encoder.sv
* find_first_set.sv -- the free tools don't seem to support the $ffs function
* priority_encoder_enable.sv 
* leading_one_trailing_one.sv 
* lfsr.sv -- one of the inputs is a vector called taps. Put a one in position where a xnor tap is needed. Refer to the lfsr_table.pdf in the docs area for more information.
* load_clear_counter.sv 
* pwm.sv
* reverse_vector.sv 
* unviersal_shift_register.sv 

### Math Specific Items
* half_adder.sv 
* full_adder.sv 
* half_subtractor.sv 
* full_subtractor.sv 
* ripple_carry_adder.sv 
* ripple_carry_subtractor.sv 
* carry_lookahead_adder.sv
* carry_lookahead_subtractor.sv 
* array_multipler.sv 
* booths_multiplier.sv 
* wallis_tree_multiplier.sv
* reciprocal_divider.sv
* sft_divider.sv


