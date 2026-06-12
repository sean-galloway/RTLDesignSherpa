# ==============================================================================
# SDC Constraints: char_top -- Timing Characterization Top-Level (ASIC only)
# ==============================================================================
#
# Target: 500 MHz (2.000 ns period) by default.
# I/O Model: 80% input delay, 20% output delay (relative to the clock period).
#
# This SDC is the ASIC-only baseline used by the open-source Yosys + OpenSTA
# flow that ships alongside it as well as by the commercial Synopsys DC /
# Cadence Genus reference scripts.  The goal is NOT to close timing -- it
# is to measure how far each combinational path falls short of, or meets,
# the target frequency so that reports can be compared across standard-cell
# libraries.
#
# Override the knobs below from your synthesis script BEFORE sourcing this
# SDC, e.g.
#     set TARGET_FREQ_MHZ 1000.0
#     source char_top.sdc
#
# ==============================================================================

# ---- Overridable parameters --------------------------------------------------
if {![info exists TARGET_FREQ_MHZ]}       { set TARGET_FREQ_MHZ        500.0 }
if {![info exists INPUT_DELAY_FRACTION]}  { set INPUT_DELAY_FRACTION   0.80  }
if {![info exists OUTPUT_DELAY_FRACTION]} { set OUTPUT_DELAY_FRACTION  0.20  }
if {![info exists CLK_UNCERTAINTY_NS]}    { set CLK_UNCERTAINTY_NS     0.100 }

# ---- Derived values ----------------------------------------------------------
set CLK_PERIOD_NS   [expr {1000.0 / $TARGET_FREQ_MHZ}]
set INPUT_DELAY_NS  [expr {$CLK_PERIOD_NS * $INPUT_DELAY_FRACTION}]
set OUTPUT_DELAY_NS [expr {$CLK_PERIOD_NS * $OUTPUT_DELAY_FRACTION}]

# ---- Clock + reset -----------------------------------------------------------
create_clock -name clk -period $CLK_PERIOD_NS [get_ports clk]
set_clock_uncertainty $CLK_UNCERTAINTY_NS [get_clocks clk]

# rst_n is asynchronous async -- the interesting paths are register-to-register.
set_false_path -from [get_ports rst_n]

# ---- LFSR seed interface -----------------------------------------------------
set_input_delay -clock clk $INPUT_DELAY_NS [get_ports i_seed_valid]
set_input_delay -clock clk $INPUT_DELAY_NS [get_ports {i_seed_data[*]}]

# ---- Output delays -- all FUB outputs ---------------------------------------
foreach p {
    o_nand o_inverter o_xor o_mux o_queue_valid
    {o_carry[*]} {o_mult[*]} {o_queue_data[*]} {o_queue_count[*]}
    {o_clk_div[*]} {o_gray_bin[*]} {o_gray_code[*]}
} {
    set_output_delay -clock clk $OUTPUT_DELAY_NS [get_ports $p]
}

# ---- Per-FUB path groups -- enable report_timing -group <name> ---------------
# DC: -from is the source of the path (the generate-block cells that drive the
# combinational logic under test).  Genus accepts the same syntax.
group_path -name GRP_NAND     -from [get_cells -hier gen_nand/*]
group_path -name GRP_INVERTER -from [get_cells -hier gen_inv/*]
group_path -name GRP_XOR      -from [get_cells -hier gen_xor/*]
group_path -name GRP_CARRY    -from [get_cells -hier gen_carry/*]
group_path -name GRP_MULT     -from [get_cells -hier gen_mult/*]
group_path -name GRP_MUX      -from [get_cells -hier gen_mux/*]
group_path -name GRP_QUEUE    -from [get_cells -hier gen_queue/*]
group_path -name GRP_CLKDIV   -from [get_cells -hier gen_clkdiv/*]
group_path -name GRP_GRAY     -from [get_cells -hier gen_gray/*]

# ---- Belt-and-suspenders dont_touch on the chain nets -----------------------
# The RTL already carries (* dont_touch = "true" *) on every chain wire; the
# SDC reinforcement guarantees the constraint flows into tools that read
# attributes lazily.
set_dont_touch [get_nets -hier gen_nand/*]
set_dont_touch [get_nets -hier gen_inv/*]
set_dont_touch [get_nets -hier gen_xor/*]
set_dont_touch [get_nets -hier gen_carry/*]
set_dont_touch [get_nets -hier gen_mult/*]
set_dont_touch [get_nets -hier gen_mux/*]

# ==============================================================================
# End of SDC
# ==============================================================================
