#==============================================================================
# impl_physopt_rerun.tcl — re-run implementation ONLY with phys_opt enabled,
# reusing the existing synth_1 result. Used to measure the phys_opt timing
# win without paying for a full resynthesis.
#==============================================================================
set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]
set project_file "$project_root/build/vivado_project/stream_char.xpr"

open_project $project_file

if {[get_property PROGRESS [get_runs synth_1]] != "100%"} {
    puts stderr "ERROR: synth_1 is not complete — run a full build first."
    exit 1
}

# Enable pre- and post-route physical optimization on the impl run.
set_property STEPS.PHYS_OPT_DESIGN.IS_ENABLED true [get_runs impl_1]
set_property STEPS.POST_ROUTE_PHYS_OPT_DESIGN.IS_ENABLED true [get_runs impl_1]

reset_run impl_1
launch_runs impl_1 -to_step write_bitstream -jobs 4
wait_on_run impl_1
if {[get_property PROGRESS [get_runs impl_1]] != "100%"} {
    puts stderr "ERROR: implementation / bitstream failed."
    exit 1
}

# ---- Post-route reports (same set as build_all.tcl) ----
open_run impl_1
set rpt_dir "$project_root/reports"
file mkdir $rpt_dir
report_utilization         -file "$rpt_dir/utilization_impl.txt"
report_timing_summary      -file "$rpt_dir/timing_summary.txt"
report_timing -sort_by group -max_paths 20 -path_type summary \
                            -file "$rpt_dir/timing_worst.txt"

report_timing -setup \
    -slack_lesser_than 0 \
    -max_paths 100000 \
    -nworst 1 \
    -sort_by slack \
    -input_pins \
    -file "$rpt_dir/timing_failing_setup_full.txt"

set fail_paths [get_timing_paths -setup -slack_lesser_than 0 \
                                 -max_paths 100000 -nworst 1 -sort_by slack]
set hot [dict create]
foreach p $fail_paths {
    set ep     [get_property ENDPOINT_PIN $p]
    set cell   [file dirname $ep]
    set parent [file dirname $cell]
    dict incr hot $parent
}
set fh [open "$rpt_dir/timing_failing_hotspots.txt" "w"]
puts $fh "# Failing-endpoint count per parent instance (descending) — post-route"
puts $fh "# count  parent_instance"
set sorted [lsort -stride 2 -index 1 -integer -decreasing $hot]
foreach {inst cnt} $sorted {
    puts $fh [format "%6d  %s" $cnt $inst]
}
close $fh

# ---- Copy bitstream into committed location ----
set bit_src "$project_root/build/vivado_project/stream_char.runs/impl_1/stream_char_top.bit"
set bit_dst "$project_root/bitstream/stream_char.bit"
file mkdir "$project_root/bitstream"
if {[file exists $bit_src]} {
    file copy -force $bit_src $bit_dst
    puts "\nBitstream: $bit_dst"
}
puts "impl_physopt_rerun complete."
