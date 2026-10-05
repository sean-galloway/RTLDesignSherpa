#==============================================================================
# build_all.tcl -- synth + impl + bitstream for bch_loop
#==============================================================================
# Run via `make bitstream`, which exports the layout env vars and calls this.
# Modeled on the Reed-Solomon harness's build_all.tcl.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]

puts "========================================================================"
puts "Binary BCH loop harness -- Full Build"
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

# Failing setup paths with node detail, plus a grouped hotspot count -- the
# per-endpoint answer to "where does it fail" without reopening the project.
report_timing -setup -slack_lesser_than 0 -max_paths 2000 -nworst 1 -sort_by slack \
              -input_pins -file "$rpt_dir/timing_failing_paths.txt"
set fh [open "$rpt_dir/timing_failing_endpoints.txt" "w"]
puts $fh "slack_ns,levels,startpoint,endpoint"
foreach p [get_timing_paths -setup -slack_lesser_than 0 -max_paths 2000 -nworst 1 -sort_by slack] {
    puts $fh "[get_property SLACK $p],[get_property LOGIC_LEVELS $p],[get_property STARTPOINT_PIN $p],[get_property ENDPOINT_PIN $p]"
}
close $fh
set hot [dict create]
foreach p [get_timing_paths -setup -slack_lesser_than 0 -max_paths 2000 -nworst 1 -sort_by slack] {
    set ep [get_property ENDPOINT_PIN $p]
    dict incr hot [file dirname [file dirname $ep]]
}
set fh [open "$rpt_dir/timing_failing_hotspots.txt" "w"]
puts $fh "# Failing-endpoint count per parent instance (descending) -- post-route"
puts $fh "# count  parent_instance"
foreach {inst cnt} [lsort -stride 2 -index 1 -integer -decreasing $hot] {
    puts $fh [format "%6d  %s" $cnt $inst]
}
close $fh

# ---- Copy bitstream to the location the Makefile names ----
set top_name [get_property top [get_filesets sources_1]]
set bit_src "$project_root/build/vivado_project/${project_name}.runs/impl_1/${top_name}.bit"
set bit_dst [expr {[info exists ::env(FPGA_BITSTREAM)] \
                   ? $::env(FPGA_BITSTREAM) \
                   : "$project_root/bitstream/bch_loop.bit"}]
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
