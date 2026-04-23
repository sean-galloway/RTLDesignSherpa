#==============================================================================
# build_all.tcl — synth + impl + bitstream for stream_char
#==============================================================================
# Usage:  REPO_ROOT=... vivado -mode batch -source build_all.tcl
# Run via `make bitstream` which sets the env vars and calls this.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]
set project_file "$project_root/vivado_project/stream_char.xpr"

puts "========================================================================"
puts "STREAM Characterization — Full Build"
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

# Utilization report immediately after synthesis — resource fit check,
# independent of implementation success/failure.
file mkdir "$project_root/reports"
open_run synth_1 -name synth_1
report_utilization -file "$project_root/reports/utilization_synth.txt"

# Close the synth open_run so impl can proceed cleanly.
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
puts "\n--- Reports ---"
open_run impl_1
report_utilization         -file "$project_root/reports/utilization_impl.txt"
report_timing_summary      -file "$project_root/reports/timing_summary.txt"
report_timing -sort_by group -max_paths 20 -path_type summary \
                            -file "$project_root/reports/timing_worst.txt"
report_clock_interaction   -file "$project_root/reports/clock_interaction.txt"
report_cdc                 -file "$project_root/reports/cdc.txt"
report_drc                 -file "$project_root/reports/drc.txt"
report_power               -file "$project_root/reports/power.txt"

# ---- Copy bitstream to the project root for easy access ----
set bit_src "$project_root/vivado_project/stream_char.runs/impl_1/stream_char_top.bit"
set bit_dst "$project_root/stream_char.bit"
if {[file exists $bit_src]} {
    file copy -force $bit_src $bit_dst
    puts "\nBitstream: $bit_dst"
} else {
    puts stderr "WARNING: bitstream not found at $bit_src"
}

puts "========================================================================"
puts "Build complete. Reports in $project_root/reports/"
puts "========================================================================"
