#==============================================================================
# build_all.tcl -- synth + impl + bitstream for the Genesys 2 LiteDRAM board proof
#==============================================================================
# Run via `make bitstream`, which sets the env vars and calls this.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]

puts "========================================================================"
puts "Genesys 2 LiteDRAM DDR3 -- Full Build"
puts "========================================================================"

# (Re)create the project so a clean re-run picks up RTL / XDC edits.
source "$script_dir/create_project.tcl"

puts "\n--- Synthesis ---"
reset_run synth_1
launch_runs synth_1 -jobs 4
wait_on_run synth_1
if {[get_property PROGRESS [get_runs synth_1]] != "100%"} {
    puts stderr "ERROR: synthesis failed."
    exit 1
}
file mkdir "$project_root/reports"
open_run synth_1 -name synth_1
report_utilization -file "$project_root/reports/utilization_synth.txt"
close_design

# ---- Implementation + bitstream ----
# No exotic directives. Unlike the pumice DDR2 build -- which sits on a +31 ps
# knife-edge at 75 MHz and needs AltSpreadLogic_high plus aggressive phys-opt to
# close -- this design is a LiteDRAM core alone on a K325T at 100 MHz. If THIS
# needs directive tuning, something is wrong that tuning should not hide.
puts "\n--- Implementation ---"
set_property STEPS.PHYS_OPT_DESIGN.IS_ENABLED true [get_runs impl_1]
launch_runs impl_1 -to_step write_bitstream -jobs 4
wait_on_run impl_1
if {[get_property PROGRESS [get_runs impl_1]] != "100%"} {
    puts stderr "ERROR: implementation / bitstream failed."
    exit 1
}

# ---- Post-route reports ----
open_run impl_1
report_timing_summary -file "$project_root/reports/timing_summary.txt"
report_utilization    -file "$project_root/reports/utilization_impl.txt"

# Say the verdict out loud. "Did it close?" must not require opening a report.
set wns [get_property SLACK [get_timing_paths -delay_type max]]
set whs [get_property SLACK [get_timing_paths -delay_type min]]
puts "========================================================================"
puts [format "  WNS = %.3f ns    WHS = %.3f ns" $wns $whs]
if {$wns < 0 || $whs < 0} {
    puts "  TIMING NOT MET -- this design should close comfortably; investigate"
    puts "  rather than reaching for impl directives."
} else {
    puts "  timing met"
}
puts "========================================================================"

# The Makefile is the single authority on the artifact name.
set bit [expr {[info exists ::env(FPGA_BITSTREAM)] ? $::env(FPGA_BITSTREAM) \
               : "$project_root/bitstream/litedram_ddr3.bit"}]
file mkdir [file dirname $bit]
# Locate the run's bitstream rather than reconstructing its path.
set produced [glob -nocomplain "$project_root/build/vivado_project/*.runs/impl_1/*.bit"]
if {[llength $produced] == 0} {
    puts stderr "ERROR: no .bit produced under impl_1"
    exit 1
}
file copy -force [lindex $produced 0] $bit
puts "Bitstream: $bit"
