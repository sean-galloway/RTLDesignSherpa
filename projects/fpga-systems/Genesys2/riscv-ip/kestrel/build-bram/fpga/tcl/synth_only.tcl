#==============================================================================
# synth_only.tcl -- synthesis + utilization + post-synth timing (make synth)
#==============================================================================
# The fast "does it fit / does 100 MHz look closable" pass, without place
# and route. Reports land in fpga/reports.
#==============================================================================

set script_dir [file dirname [file normalize [info script]]]
source "$script_dir/create_project.tcl"

puts "\n--- Synthesis only ---"
reset_run synth_1
launch_runs synth_1 -jobs 8
wait_on_run synth_1
if {[get_property PROGRESS [get_runs synth_1]] != "100%"} {
    puts stderr "ERROR: synthesis failed."
    exit 1
}

file mkdir $rpt_dir
open_run synth_1 -name synth_1
report_utilization -hierarchical -hierarchical_depth 4 -file "$rpt_dir/utilization_hier_synth.txt"
report_utilization    -file "$rpt_dir/utilization_synth.txt"
report_timing_summary -file "$rpt_dir/timing_summary_synth.txt"
report_timing -setup -max_paths 20 -nworst 1 -sort_by slack -input_pins \
              -file "$rpt_dir/timing_worst_paths_synth.txt"
puts "Synthesis reports in $rpt_dir"
