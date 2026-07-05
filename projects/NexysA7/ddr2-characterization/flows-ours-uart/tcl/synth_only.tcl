#==============================================================================
# synth_only.tcl — run synthesis and emit utilization + failing-path report
#==============================================================================
# For fast "will this fit?" / "does 100 MHz close?" iteration without paying
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
report_utilization    -file "$project_root/reports/utilization_synth.txt"
report_timing_summary -file "$project_root/reports/timing_summary_synth.txt"

set rpt_dir "$project_root/reports"

# Every failing setup path — one per endpoint, worst slack first.
report_timing -setup \
    -slack_lesser_than 0 \
    -max_paths 100000 \
    -nworst 1 \
    -sort_by slack \
    -input_pins \
    -file "$rpt_dir/timing_failing_setup_full.txt"

# Compact CSV of failing endpoints (slack, levels, source, dest) — easy to
# histogram / grep for repeat offenders.
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

# Failing endpoints grouped by parent instance — which RTL block owns the
# most failing paths?
set hot [dict create]
foreach p $fail_paths {
    set ep     [get_property ENDPOINT_PIN $p]
    set cell   [file dirname $ep]
    set parent [file dirname $cell]
    dict incr hot $parent
}
set fh [open "$rpt_dir/timing_failing_hotspots.txt" "w"]
puts $fh "# Failing-endpoint count per parent instance (descending) — post-synth"
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
puts "  $rpt_dir/timing_failing_setup_full.txt   (every failing setup path)"
puts "  $rpt_dir/timing_failing_endpoints.csv    (compact per-endpoint list)"
puts "  $rpt_dir/timing_failing_hotspots.txt     (failing endpoints per instance)"
puts "========================================================================"
