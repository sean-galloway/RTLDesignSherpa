#==============================================================================
# synth_only.tcl -- run synthesis and emit utilization + timing reports
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]

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

set rpt_dir "$project_root/reports"
report_timing -setup \
    -slack_lesser_than 0 \
    -max_paths 100000 \
    -nworst 1 \
    -sort_by slack \
    -input_pins \
    -file "$rpt_dir/timing_failing_setup_full.txt"

set fail_paths [get_timing_paths -setup -slack_lesser_than 0 \
                                 -max_paths 100000 -nworst 1 -sort_by slack]
set fh [open "$rpt_dir/timing_failing_endpoints.csv" "w"]
puts $fh "slack_ns,levels,startpoint,endpoint"
foreach p $fail_paths {
    set slack  [get_property SLACK         $p]
    set levels [get_property LOGIC_LEVELS  $p]
    set src    [get_property STARTPOINT_PIN $p]
    set dst    [get_property ENDPOINT_PIN   $p]
    puts $fh "$slack,$levels,$src,$dst"
}
close $fh

set hot [dict create]
foreach p $fail_paths {
    set ep   [get_property ENDPOINT_PIN $p]
    set cell [file dirname $ep]
    set parent [file dirname $cell]
    dict incr hot $parent
}
set fh [open "$rpt_dir/timing_failing_hotspots.txt" "w"]
puts $fh "# Failing-endpoint count per parent instance (descending)"
puts $fh "# count  parent_instance"
set sorted [lsort -stride 2 -index 1 -integer -decreasing $hot]
foreach {inst cnt} $sorted {
    puts $fh [format "%6d  %s" $cnt $inst]
}
close $fh

puts "========================================================================"
puts "Synthesis complete."
puts "Reports:"
puts "  $rpt_dir/utilization_synth.txt"
puts "  $rpt_dir/timing_summary_synth.txt"
puts "  $rpt_dir/timing_failing_setup_full.txt"
puts "  $rpt_dir/timing_failing_endpoints.csv"
puts "  $rpt_dir/timing_failing_hotspots.txt"
puts "========================================================================"
