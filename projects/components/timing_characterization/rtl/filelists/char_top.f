// Filelist: char_top
// Description: Top-level timing characterization wrapper (flat - all sources listed)

// Include directories
+incdir+common

// Dependencies from local rtl/common/ - primitives
common/counter_bin.sv
common/fifo_control.sv
common/counter_bingray.sv
common/clock_divider.sv
common/gaxi_fifo_sync.sv

// Dependencies from local rtl/common/ - multiplier primitives
common/math_adder_half.sv
common/math_adder_full.sv
common/math_adder_carry_save.sv
common/math_compressor_4to2.sv

// Dependencies from local rtl/common/ - prefix adder primitives (for Dadda 4:2)
common/math_prefix_cell.sv
common/math_prefix_cell_gray.sv
common/math_adder_han_carlson_016.sv
common/math_adder_han_carlson_022.sv
common/math_adder_han_carlson_048.sv

// Dependencies from local rtl/common/ - Dadda tree multipliers
common/math_multiplier_dadda_tree_008.sv
common/math_multiplier_dadda_tree_016.sv
common/math_multiplier_dadda_tree_032.sv

// Dependencies from local rtl/common/ - Wallace tree multipliers
common/math_multiplier_wallace_tree_008.sv
common/math_multiplier_wallace_tree_016.sv
common/math_multiplier_wallace_tree_032.sv

// Dependencies from local rtl/common/ - Wallace tree CSA multipliers
common/math_multiplier_wallace_tree_csa_008.sv
common/math_multiplier_wallace_tree_csa_016.sv
common/math_multiplier_wallace_tree_csa_032.sv

// Dependencies from local rtl/common/ - Dadda 4:2 compressor multipliers
common/math_multiplier_dadda_4to2_008.sv
common/math_multiplier_dadda_4to2_011.sv
common/math_multiplier_dadda_4to2_024.sv

// FUB sources
fub/nand_chain.sv
fub/inverter_chain.sv
fub/xor_tree.sv
fub/carry_chain.sv
fub/multiplier_tree.sv
fub/mux_tree.sv
fub/queue_depth.sv
fub/clock_divider_chain.sv
fub/gray_counter_chain.sv

// Top-level
top/char_top.sv
