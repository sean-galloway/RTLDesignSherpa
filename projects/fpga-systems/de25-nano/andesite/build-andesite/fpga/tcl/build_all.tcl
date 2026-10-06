#==============================================================================
# build_all.tcl -- synth + impl + bitstream for the andesite skeleton,
# Genesys 2 (de25-nano area)
#==============================================================================
# Run via `make bitstream`, which sets the env vars and calls this.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]

puts "========================================================================"
puts "andesite skeleton on Genesys 2 -- Full Build"
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
# No exotic directives: this is a controller skeleton at 100 MHz on a K325T.
# If it misses badly, the answer is the andesite RTL's timing picture (which
# is what this build exists to learn), not directive tuning.
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
    puts "  TIMING NOT MET -- record the miss; it is the experiment's output."
} else {
    puts "  timing met"
}
puts "========================================================================"
