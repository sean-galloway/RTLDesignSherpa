# File List
These are some fairly random, but somewhat useful set of basic verilog functions.
Arguably, the math related ones aren't useful other than to study.
----------------------------------------------------------------
### Fifo Related Files
* bin2gray.sv 
* gray2bin.sv 
* glitch_free_n_dff_arn.sv 
* sync_fifo.sv 
* async_fifo.sv 

### Arbiters
These are all parameterized.
* round_robin_arbiter.sv 
* interval_weighted_round_robin.sv 

### Miscellaneous
These are all parameterized.
* decoder.sv 
* priority_encoder_enable.sv 
* leading_one_trailing_one.sv 
* lfsr_table.pdf 
* lfsr.sv -- one of the inputs is a vector called taps. Put a one in position where a xnor tap is needed. Refer to the lfsr_table.pdf for more information.
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
* array_multipler.sv 
* booths_multiplier.sv 
* wallis_tree_multiplier.sv
