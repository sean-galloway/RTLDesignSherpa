#==============================================================================
# synth_only.tcl — synthesis-only run (no place/route)
#==============================================================================
# Useful for checking utilisation/timing-feasibility without spending 10-30
# minutes on impl + bitgen.  Outputs utilization_synth.txt.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]

source "$script_dir/create_project.tcl"

puts "\n--- Synthesis only ---"
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
report_timing_summary -file "$project_root/reports/timing_summary_synth.txt"

puts "\nUtilization: $project_root/reports/utilization_synth.txt"
puts "Timing:      $project_root/reports/timing_summary_synth.txt"
