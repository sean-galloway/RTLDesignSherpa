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

# -----------------------------------------------------------------------------
# Full failing-path detail.
#   - Every setup path with negative slack (one per endpoint, worst slack first)
#   - Compact "endpoint + slack + logic levels" listing for triage
#   - Per-cell hot list (which RTL instances own the most failing endpoints)
# -----------------------------------------------------------------------------
set rpt_dir "$project_root/reports"

# 1) Detailed timing for ALL failing setup paths (one per endpoint).
report_timing -setup \
    -slack_lesser_than 0 \
    -max_paths 100000 \
    -nworst 1 \
    -sort_by slack \
    -input_pins \
    -file "$rpt_dir/timing_failing_setup_full.txt"

# 2) Compact per-endpoint summary — slack, levels, cell counts, source/dest.
#    Easy to grep, easy to histogram.
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

# 3) Per-instance hotspot — count failing endpoints per parent cell so we can
#    see which RTL block dominates the fail list.
set hot [dict create]
foreach p $fail_paths {
    set ep   [get_property ENDPOINT_PIN $p]
    # Strip the trailing /<pin> to get the cell instance path, then take the
    # parent (drops the FF leaf so we cluster at the RTL block level).
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
puts "  $rpt_dir/timing_failing_setup_full.txt   (every failing setup path)"
puts "  $rpt_dir/timing_failing_endpoints.csv    (compact per-endpoint list)"
puts "  $rpt_dir/timing_failing_hotspots.txt     (failing endpoints per instance)"
puts "========================================================================"
