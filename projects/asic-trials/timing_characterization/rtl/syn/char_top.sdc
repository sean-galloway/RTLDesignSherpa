# ==============================================================================
# SDC Constraints: char_top - Timing Characterization Top-Level
# ==============================================================================
#
# Target: 500 MHz (2.000 ns period)
# I/O Model: 80% input delay, 20% output delay (relative to clock period)
#
# This file provides a baseline SDC for synthesizing char_top across different
# FPGA and ASIC targets. The goal is NOT to close timing -- it is to measure
# how far each combinational path falls short (or meets) the target frequency.
#
# Synthesis reports will show setup slack per path group, which is the
# primary metric for comparing gate delay across technologies.
#
# ==============================================================================

# --------------------------------------------------------------------------
# OVERRIDABLE PARAMETERS -- change these to sweep frequency / IO split
# --------------------------------------------------------------------------
# Set FLOW to select tool-specific blocks:
#   "asic"    - Synopsys DC / Cadence Genus
#   "vivado"  - Xilinx Vivado
#   "quartus" - Intel Quartus Prime
#
# Override from your synthesis script BEFORE sourcing this SDC:
#   set FLOW "vivado"
#   source char_top.sdc

if {![info exists FLOW]} {
    set FLOW "asic"
}

# Target clock frequency in MHz. 500 MHz is aggressive for most FPGA fabrics
# and will clearly expose combinational depth differences between FUBs.
if {![info exists TARGET_FREQ_MHZ]} {
    set TARGET_FREQ_MHZ 500.0
}

# Input / output delay as a fraction of the clock period.
# 80/20 split leaves 80% of the period consumed before the first flop
# (modeling a heavy external source) and 20% after the last flop
# (modeling a light external sink). This forces the combinational logic
# to close within the remaining budget and makes the reports directly
# comparable between FUBs.
if {![info exists INPUT_DELAY_FRACTION]} {
    set INPUT_DELAY_FRACTION 0.80
}
if {![info exists OUTPUT_DELAY_FRACTION]} {
    set OUTPUT_DELAY_FRACTION 0.20
}

# Clock uncertainty covers jitter + skew. Adjust per target technology.
if {![info exists CLK_UNCERTAINTY_NS]} {
    set CLK_UNCERTAINTY_NS 0.100
}

# --------------------------------------------------------------------------
# Derived values (do not edit below this line for normal sweeps)
# --------------------------------------------------------------------------
set CLK_PERIOD_NS   [expr {1000.0 / $TARGET_FREQ_MHZ}]
set INPUT_DELAY_NS  [expr {$CLK_PERIOD_NS * $INPUT_DELAY_FRACTION}]
set OUTPUT_DELAY_NS [expr {$CLK_PERIOD_NS * $OUTPUT_DELAY_FRACTION}]

# ==========================================================================
# SECTION A: Tool-Agnostic Core Constraints
# ==========================================================================

# --------------------------------------------------------------------------
# Clock definition
# --------------------------------------------------------------------------
create_clock -name clk -period $CLK_PERIOD_NS [get_ports clk]
set_clock_uncertainty $CLK_UNCERTAINTY_NS [get_clocks clk]

# --------------------------------------------------------------------------
# Reset
# --------------------------------------------------------------------------
# rst_n is asynchronous but treat it as a false path for STA -- the
# interesting paths are all synchronous register-to-register.
set_false_path -from [get_ports rst_n]

# --------------------------------------------------------------------------
# LFSR seed interface
# --------------------------------------------------------------------------
set_input_delay  -clock clk $INPUT_DELAY_NS [get_ports i_seed_valid]
set_input_delay  -clock clk $INPUT_DELAY_NS [get_ports {i_seed_data[*]}]

# --------------------------------------------------------------------------
# Output delays -- all FUB outputs
# --------------------------------------------------------------------------
set_output_delay -clock clk $OUTPUT_DELAY_NS [get_ports o_nand]
set_output_delay -clock clk $OUTPUT_DELAY_NS [get_ports o_inverter]
set_output_delay -clock clk $OUTPUT_DELAY_NS [get_ports o_xor]
set_output_delay -clock clk $OUTPUT_DELAY_NS [get_ports {o_carry[*]}]
set_output_delay -clock clk $OUTPUT_DELAY_NS [get_ports {o_mult[*]}]
set_output_delay -clock clk $OUTPUT_DELAY_NS [get_ports o_mux]
set_output_delay -clock clk $OUTPUT_DELAY_NS [get_ports {o_queue_data[*]}]
set_output_delay -clock clk $OUTPUT_DELAY_NS [get_ports o_queue_valid]
set_output_delay -clock clk $OUTPUT_DELAY_NS [get_ports {o_queue_count[*]}]
set_output_delay -clock clk $OUTPUT_DELAY_NS [get_ports {o_clk_div[*]}]
set_output_delay -clock clk $OUTPUT_DELAY_NS [get_ports {o_gray_bin[*]}]
set_output_delay -clock clk $OUTPUT_DELAY_NS [get_ports {o_gray_code[*]}]

# ==========================================================================
# SECTION B: Tool-Specific Constraints
# ==========================================================================

if {$FLOW eq "asic"} {
    # ==================================================================
    # ASIC Flow (Synopsys Design Compiler / Cadence Genus)
    # ==================================================================
    #
    # PREREQUISITES -- set these in your synthesis script BEFORE sourcing:
    #
    #   # Synopsys DC:
    #   set target_library "your_stdcell.db"
    #   set link_library   "* your_stdcell.db"
    #   set_operating_conditions -max WC_COM  ;# worst-case commercial
    #
    #   # Cadence Genus:
    #   set_db init_lib_search_path /path/to/libs
    #   read_libs your_stdcell.lib
    #
    #   set FLOW "asic"
    #   source char_top.sdc
    #

    # -- I/O Models -------------------------------------------------------
    # Replace BUFX4 with an appropriate buffer from your target library.
    # set_driving_cell -lib_cell BUFX4 -pin Y [all_inputs]
    # set_load 0.050 [all_outputs]    ;# 50 fF typical gate load

    # -- Path Groups for Per-FUB Reporting --------------------------------
    # These enable report_timing -group <name> for per-FUB slack.
    group_path -name GRP_NAND     -from [get_cells -hier gen_nand/*]
    group_path -name GRP_INVERTER -from [get_cells -hier gen_inv/*]
    group_path -name GRP_XOR      -from [get_cells -hier gen_xor/*]
    group_path -name GRP_CARRY    -from [get_cells -hier gen_carry/*]
    group_path -name GRP_MULT     -from [get_cells -hier gen_mult/*]
    group_path -name GRP_MUX      -from [get_cells -hier gen_mux/*]
    group_path -name GRP_QUEUE    -from [get_cells -hier gen_queue/*]
    group_path -name GRP_CLKDIV   -from [get_cells -hier gen_clkdiv/*]
    group_path -name GRP_GRAY     -from [get_cells -hier gen_gray/*]

    # -- Dont-Touch (reinforce RTL attributes) ----------------------------
    set_dont_touch [get_nets -hier gen_nand/*]
    set_dont_touch [get_nets -hier gen_inv/*]
    set_dont_touch [get_nets -hier gen_xor/*]
    set_dont_touch [get_nets -hier gen_carry/*]
    set_dont_touch [get_nets -hier gen_mult/*]
    set_dont_touch [get_nets -hier gen_mux/*]

} elseif {$FLOW eq "vivado"} {
    # ==================================================================
    # Xilinx Vivado Flow
    # ==================================================================
    #
    # PREREQUISITES -- set these in your Vivado Tcl script:
    #
    #   set_property part xc7a200tffg1156-2 [current_project]
    #   # Or for UltraScale+:
    #   # set_property part xcvu9p-flga2104-2L-e [current_project]
    #
    #   set FLOW "vivado"
    #   read_xdc char_top.sdc          ;# or rename to .xdc
    #
    #   # Synthesis settings:
    #   synth_design -top char_top \
    #       -generic EN_NAND_TREE=1 \
    #       -generic EN_INVERTER_CHAIN=1 \
    #       ...
    #

    # -- I/O Models -------------------------------------------------------
    # Vivado uses IOSTANDARD properties rather than driving cell.
    # Uncomment and set appropriately for your target board:
    # set_property IOSTANDARD LVCMOS33 [all_inputs]
    # set_property IOSTANDARD LVCMOS33 [all_outputs]
    set_load 5.0 [all_outputs]

    # -- DONT_TOUCH (reinforce RTL (* dont_touch *) attributes) -----------
    # Vivado property syntax -- applied to nets within generate blocks.
    # These are belt-and-suspenders; the RTL attributes should suffice.
    # Uncomment if Vivado strips the RTL attributes:
    # set_property DONT_TOUCH true [get_nets -hier -filter {NAME =~ *gen_nand*}]
    # set_property DONT_TOUCH true [get_nets -hier -filter {NAME =~ *gen_inv*}]
    # set_property DONT_TOUCH true [get_nets -hier -filter {NAME =~ *gen_xor*}]
    # set_property DONT_TOUCH true [get_nets -hier -filter {NAME =~ *gen_carry*}]
    # set_property DONT_TOUCH true [get_nets -hier -filter {NAME =~ *gen_mult*}]
    # set_property DONT_TOUCH true [get_nets -hier -filter {NAME =~ *gen_mux*}]

} elseif {$FLOW eq "quartus"} {
    # ==================================================================
    # Intel Quartus Prime Flow
    # ==================================================================
    #
    # PREREQUISITES -- set these in your .qsf file or Tcl script:
    #
    #   set_global_assignment -name FAMILY "Cyclone 10 LP"
    #   set_global_assignment -name DEVICE 10CL120YF780I7G
    #   # Or for Stratix 10:
    #   # set_global_assignment -name FAMILY "Stratix 10"
    #   # set_global_assignment -name DEVICE 1SG280HU2F50E2VG
    #
    #   set_global_assignment -name SDC_FILE char_top.sdc
    #   set_global_assignment -name OPTIMIZATION_MODE "HIGH PERFORMANCE EFFORT"
    #
    #   # In a pre-SDC Tcl hook:
    #   set FLOW "quartus"
    #
    #   # I/O standard for all pins:
    #   set_global_assignment -name STRATIX_DEVICE_IO_STANDARD "2.5 V"
    #

    # -- I/O Models -------------------------------------------------------
    set_load 5.0 [all_outputs]

    # -- Preserve (reinforce RTL /* synthesis preserve */ attributes) ------
    # Quartus uses "preserve" pragmas in RTL. SDC-side reinforcement:
    # Uncomment if Quartus strips the RTL attributes:
    # set_instance_assignment -name PRESERVE_REGISTER ON -to *gen_nand*
    # set_instance_assignment -name PRESERVE_REGISTER ON -to *gen_inv*
    # set_instance_assignment -name PRESERVE_REGISTER ON -to *gen_xor*
    # set_instance_assignment -name PRESERVE_REGISTER ON -to *gen_carry*
    # set_instance_assignment -name PRESERVE_REGISTER ON -to *gen_mult*
    # set_instance_assignment -name PRESERVE_REGISTER ON -to *gen_mux*

} else {
    puts "WARNING: Unknown FLOW '$FLOW'. Expected 'asic', 'vivado', or 'quartus'."
    puts "         Using tool-agnostic constraints only (no path groups or I/O models)."
}

# ==========================================================================
# SECTION C: Reporting Helpers (copy-paste into your synthesis script)
# ==========================================================================
#
# -- ASIC (DC / Genus) ---------------------------------------------------
#   report_timing -group GRP_NAND     -max_paths 1
#   report_timing -group GRP_INVERTER -max_paths 1
#   report_timing -group GRP_XOR      -max_paths 1
#   report_timing -group GRP_CARRY    -max_paths 1
#   report_timing -group GRP_MULT     -max_paths 1
#   report_timing -group GRP_MUX      -max_paths 1
#   report_timing -group GRP_QUEUE    -max_paths 1
#   report_timing -group GRP_CLKDIV   -max_paths 1
#   report_timing -group GRP_GRAY     -max_paths 1
#   report_area -hierarchy
#
# -- Vivado ---------------------------------------------------------------
#   report_timing_summary -delay_type max -max_paths 10
#   report_utilization -hierarchical
#   report_timing -from [get_cells -hier gen_nand/*] -max_paths 1
#   report_timing -from [get_cells -hier gen_carry/*] -max_paths 1
#   # ... repeat for each FUB
#
# -- Quartus (TimeQuest) --------------------------------------------------
#   report_timing -setup -npaths 10
#   report_timing -from [get_registers *gen_nand*] -npaths 1
#   report_timing -from [get_registers *gen_carry*] -npaths 1
#   # ... repeat for each FUB
#   report_fitter_resource_usage
#
# ==============================================================================
# End of SDC
# ==============================================================================
