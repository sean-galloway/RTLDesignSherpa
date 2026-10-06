#==============================================================================
# build_all.tcl -- synth + impl + bitstream for cdc_counter_display
#==============================================================================
# Run via `make bitstream`, which exports the layout env vars and calls this.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]

puts "========================================================================"
puts "CDC counter display (phase-1) -- Full Build"
puts "========================================================================"

# (Re)create the project so a clean re-run picks up RTL / XDC edits.
source "$script_dir/create_project.tcl"

# ---- Synthesis ----
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
puts "\n--- Implementation ---"
launch_runs impl_1 -to_step write_bitstream -jobs 4
wait_on_run impl_1
if {[get_property PROGRESS [get_runs impl_1]] != "100%"} {
    puts stderr "ERROR: implementation / bitstream failed."
    exit 1
}

# ---- Post-route reports ----
open_run impl_1
set rpt_dir "$project_root/reports"
report_utilization         -file "$rpt_dir/utilization_impl.txt"
report_timing_summary      -file "$rpt_dir/timing_summary.txt"
report_clock_interaction   -file "$rpt_dir/clock_interaction.txt"
report_cdc                 -file "$rpt_dir/cdc.txt"
report_drc                 -file "$rpt_dir/drc.txt"

# ---- Copy bitstream to the location the Makefile names ----
set bit_src "$project_root/build/vivado_project/cdc_counter_display.runs/impl_1/cdc_counter_display_top.bit"
set bit_dst [expr {[info exists ::env(FPGA_BITSTREAM)] \
                   ? $::env(FPGA_BITSTREAM) \
                   : "$project_root/bitstream/cdc_counter_display.bit"}]
file mkdir [file dirname $bit_dst]
if {[file exists $bit_src]} {
    file copy -force $bit_src $bit_dst
    puts "\nBitstream: $bit_dst"
} else {
    puts stderr "WARNING: bitstream not found at $bit_src"
}

puts "========================================================================"
puts "Build complete. Reports in $rpt_dir/"
puts "========================================================================"
