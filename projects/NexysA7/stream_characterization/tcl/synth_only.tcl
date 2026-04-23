#==============================================================================
# synth_only.tcl — run synthesis and emit utilization report, skip impl
#==============================================================================
# For fast "will this fit?" / "is the build clean?" iteration without paying
# for place+route. Invoked by `make synth`.
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
report_utilization       -file "$project_root/reports/utilization_synth.txt"
report_timing_summary    -file "$project_root/reports/timing_summary_synth.txt"

puts "========================================================================"
puts "Synthesis complete."
puts "Reports:"
puts "  $project_root/reports/utilization_synth.txt"
puts "  $project_root/reports/timing_summary_synth.txt"
puts "========================================================================"
