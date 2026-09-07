# ==============================================================================
# Cadence Genus driver for char_top (commercial ASIC flow).
# Reference / starting point; adapt to your PDK and corner setup.
#
#   genus -files genus_synth.tcl
# ==============================================================================

set TOP             char_top
set SYN_ROOT        [file normalize [file dirname [info script]]]
set RTL_ROOT        [file normalize $SYN_ROOT/..]
set FILELIST        $RTL_ROOT/filelists/char_top.f
set TARGET_FREQ_MHZ 500.0

# ---- PDK setup (edit to taste) ----------------------------------------------
# set_db init_lib_search_path /path/to/your/libs
# read_libs your_stdcell.lib
# read_lef  your_stdcell.lef
# set_db operating_condition typical

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
read_hdl -sv $sources
elaborate $TOP
current_design $TOP

# ---- Constraints + dont_touch ------------------------------------------------
source $SYN_ROOT/char_top.sdc

# ---- Compile -----------------------------------------------------------------
syn_generic
syn_map
syn_opt

# ---- Reports -----------------------------------------------------------------
file mkdir $SYN_ROOT/build/reports
foreach grp {GRP_NAND GRP_INVERTER GRP_XOR GRP_CARRY GRP_MULT \
             GRP_MUX  GRP_QUEUE    GRP_CLKDIV GRP_GRAY} {
    redirect $SYN_ROOT/build/reports/${grp}.rpt {
        report_timing -group $grp -max_paths 1
    }
}
redirect $SYN_ROOT/build/reports/area.rpt  { report_area -depth 8 }
redirect $SYN_ROOT/build/reports/gates.rpt { report_gates }
redirect $SYN_ROOT/build/reports/power.rpt { report_power }

write_hdl > $SYN_ROOT/build/${TOP}.netlist.v
write_sdc > $SYN_ROOT/build/${TOP}.sdc.out
puts "Genus: build/${TOP}.netlist.v + reports/"
exit
