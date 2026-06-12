# ==============================================================================
# Synopsys Design Compiler driver for char_top (commercial ASIC flow).
# Reference / starting point; adapt to your PDK and corner setup.
#
#   dc_shell -f dc_synth.tcl
# ==============================================================================

set TOP             char_top
set SYN_ROOT        [file normalize [file dirname [info script]]]
set RTL_ROOT        [file normalize $SYN_ROOT/..]
set FILELIST        $RTL_ROOT/filelists/char_top.f
set TARGET_FREQ_MHZ 500.0

# ---- PDK setup (edit to taste) ----------------------------------------------
# set target_library "your_stdcell_typ.db"
# set link_library   "* your_stdcell_typ.db"
# set_operating_conditions -max WC_COM -min BC_COM
# set_wire_load_mode top

# ---- Source list -------------------------------------------------------------
set sources [list]
set fh [open $FILELIST r]
while {[gets $fh line] >= 0} {
    set t [string trim $line]
    if {$t eq "" || [string match "//*" $t] || [string match "+incdir*" $t]} {
        continue
    }
    lappend sources $RTL_ROOT/$t
}
close $fh

# ---- Read + elaborate --------------------------------------------------------
analyze -format sverilog -define { } $sources
elaborate $TOP -architecture verilog
current_design $TOP
link

# ---- Constraints + dont_touch ------------------------------------------------
source $SYN_ROOT/char_top.sdc

# ---- Compile -----------------------------------------------------------------
set_app_var compile_ultra_ungroup_dw false
compile_ultra -no_autoungroup -no_boundary_optimization

# ---- Reports -----------------------------------------------------------------
file mkdir $SYN_ROOT/build/reports
foreach grp {GRP_NAND GRP_INVERTER GRP_XOR GRP_CARRY GRP_MULT \
             GRP_MUX  GRP_QUEUE    GRP_CLKDIV GRP_GRAY} {
    redirect $SYN_ROOT/build/reports/${grp}.rpt {
        report_timing -group $grp -max_paths 1 -delay max -nworst 1 \
                      -nets -capacitance -transition_time
    }
}
redirect $SYN_ROOT/build/reports/area.rpt   { report_area -hierarchy }
redirect $SYN_ROOT/build/reports/qor.rpt    { report_qor }
redirect $SYN_ROOT/build/reports/power.rpt  { report_power }

write -format ddc -hierarchy -output $SYN_ROOT/build/${TOP}.ddc
write -format verilog -hierarchy -output $SYN_ROOT/build/${TOP}.netlist.v
puts "DC: build/${TOP}.netlist.v + reports/"
exit
