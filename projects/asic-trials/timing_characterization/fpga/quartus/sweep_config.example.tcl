# ==============================================================================
# Example sweep configuration for fpga/quartus/syn_sweep_quartus.tcl
# ==============================================================================
# Plain Tcl `set` statements. Copy this file, edit, and pass its path:
#
#   cd fpga && make quartus-sweep QUARTUS_CFG=quartus/my_sweep.tcl
#   # or directly:
#   quartus_sh -t quartus/syn_sweep_quartus.tcl quartus/my_sweep.tcl
#
# Every key below has the default shown; omit any you do not change. Paths
# are relative to the timing_characterization/ root unless absolute.
# ==============================================================================

# -- Target device ------------------------------------------------------------
# Quartus Prime Lite 24.1std ships the Cyclone V and MAX 10 families only
# (`get_family_list`). 5CGXFC5C6F27C7 is the Cyclone V GX Starter Kit part
# (28 nm, a fair peer of the Artix-7 the Vivado flow targets). char_top has
# 242 top-level pins with every FUB enabled, which does NOT fit the DE1-SoC
# 5CSEMA5F31C6 (most of its I/O belongs to the HPS) unless VIRTUAL_PINS is 1.
# A Standard/Pro install widens the choice.
set FAMILY  "Cyclone V"
set DEVICE  5CGXFC5C6F27C7

# -- Sweep points (MHz). One full map+fit+sta per point, run in order. ---------
set FREQS_MHZ {100 150 200 250 300}

# -- Design -------------------------------------------------------------------
set TOP        char_top
set FILELIST   rtl/filelists/char_top.f       ;# expanded by fpga/tcl/filelist_utils.tcl
set MASTER_SDC rtl/syn/char_top.sdc           ;# the multi-flow SDC; FLOW is forced to "quartus"

# Top-level parameter overrides, as {NAME VALUE ...}. Empty = RTL defaults
# (all nine FUBs enabled). Example: a carry-width sweep at one frequency:
#   set FREQS_MHZ {200}
#   set PARAMETERS {CARRY_WIDTH 128 EN_MULTIPLIER 0}
set PARAMETERS {}

# -- Constraint model (forwarded to the master SDC) ---------------------------
set INPUT_DELAY_FRACTION  0.80
set OUTPUT_DELAY_FRACTION 0.20
set CLK_UNCERTAINTY_NS    0.100

# -- Fitter -------------------------------------------------------------------
set OPTIMIZATION_MODE "HIGH PERFORMANCE EFFORT"
set FITTER_SEED       1
# 1 = declare every top-level port a VIRTUAL_PIN (no I/O cell, no pin
# placement). Use when the top has more ports than the package has pins, or
# to measure core logic alone. 0 keeps real pins so the 80/20 I/O budget in
# the SDC lands on real I/O cells, as it does in the Vivado flow.
set VIRTUAL_PINS 0

# -- Output -------------------------------------------------------------------
# One Quartus project per point under BUILD_DIR/<F>MHz/ (git-ignored), and
# the reports worth keeping under REPORTS_DIR/sweep_<F>MHz/, which the
# aggregator turns into REPORTS_DIR/sweep_wns.csv.
set BUILD_DIR   fpga/build/quartus
set REPORTS_DIR fpga/reports/quartus
