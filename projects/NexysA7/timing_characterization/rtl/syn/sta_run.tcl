# ==============================================================================
# OpenSTA timing report for char_top.
#
# Reads the post-synth netlist Yosys emitted into $BUILD_DIR, loads the same
# Liberty file used during mapping, applies char_top.sdc, and dumps a
# per-FUB report into $BUILD_DIR/timing/.
# ==============================================================================

set TOP   $::env(TOP)
set LIB   $::env(LIB_PATH)
set BUILD $::env(BUILD_DIR)
set SYN   $::env(SYN_ROOT)

set NETLIST $BUILD/$TOP.netlist.v
set SDC     $SYN/char_top.sdc
set TIMING  $BUILD/timing
file mkdir $TIMING

read_liberty $LIB
read_verilog $NETLIST
link_design  $TOP

# TARGET_FREQ_MHZ is plumbed through env so the SDC knob lines up with
# what the synthesis run was constrained to.
if {[info exists ::env(TARGET_FREQ_MHZ)]} {
    set TARGET_FREQ_MHZ $::env(TARGET_FREQ_MHZ)
}
source $SDC

# ---- Whole-design summary ----------------------------------------------------
puts "==== WORST setup slack across all groups ===="
report_worst_slack -max

# ---- Per-FUB path-group reports ----------------------------------------------
foreach grp {GRP_NAND GRP_INVERTER GRP_XOR GRP_CARRY GRP_MULT \
             GRP_MUX  GRP_QUEUE    GRP_CLKDIV GRP_GRAY} {
    set out "$TIMING/${grp}.rpt"
    puts "==== $grp -> $out ===="
    report_checks -group_count 1 -path_group $grp -path_delay max \
                  -fields {nets cap input slew} -digits 4 \
                  > $out
    # Also print a one-liner WNS so the Makefile grep finds it.
    set wns [worst_slack -max -path_group $grp]
    puts [format "Path Group: %-13s  WNS = %.4f ns" $grp $wns]
}

# ---- Area + cell counts -----------------------------------------------------
report_design_area > $BUILD/area.rpt
puts "Chip area report written to $BUILD/area.rpt"
