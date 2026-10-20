#==============================================================================
# build_all.tcl -- synth + impl + bitstream for kestrel on block RAM
#==============================================================================
# Run via `make bitstream`. Reports land in fpga/reports; the bitstream goes where the Makefile's FPGA_BITSTREAM says.
# Modeled on the BCH loop harness's build_all.tcl.
#==============================================================================

set script_dir [file dirname [file normalize [info script]]]
source "$script_dir/create_project.tcl"

puts "\n--- Synthesis ---"
reset_run synth_1
launch_runs synth_1 -jobs 8
wait_on_run synth_1
if {[get_property PROGRESS [get_runs synth_1]] != "100%"} {
    puts stderr "ERROR: synthesis failed."
    exit 1
}
file mkdir $rpt_dir
open_run synth_1 -name synth_1
report_utilization -file "$rpt_dir/utilization_synth.txt"
close_design

puts "\n--- Implementation ---"
launch_runs impl_1 -to_step write_bitstream -jobs 8
wait_on_run impl_1
if {[get_property PROGRESS [get_runs impl_1]] != "100%"} {
    puts stderr "ERROR: implementation / bitstream failed."
    exit 1
}

open_run impl_1
report_utilization                -file "$rpt_dir/utilization_impl.txt"
report_utilization -hierarchical -hierarchical_depth 4 -file "$rpt_dir/utilization_hier_impl.txt"
report_timing_summary             -file "$rpt_dir/timing_summary.txt"
report_clock_interaction          -file "$rpt_dir/clock_interaction.txt"
report_drc                        -file "$rpt_dir/drc.txt"
report_timing -setup -max_paths 20 -nworst 1 -sort_by slack -input_pins \
              -file "$rpt_dir/timing_worst_paths.txt"

set hot [dict create]
foreach p [get_timing_paths -setup -slack_lesser_than 0 -max_paths 2000 -nworst 1 -sort_by slack] {
    dict incr hot [file dirname [file dirname [get_property ENDPOINT_PIN $p]]]
}
set fh [open "$rpt_dir/timing_failing_hotspots.txt" "w"]
puts $fh "# Failing-endpoint count per parent instance (descending) -- post-route"
foreach {inst cnt} [lsort -stride 2 -index 1 -integer -decreasing $hot] {
    puts $fh [format "%6d  %s" $cnt $inst]
}
close $fh

set top_name [get_property top [get_filesets sources_1]]
set bit_src "$project_root/build/vivado_project/${project_name}.runs/impl_1/${top_name}.bit"
set bit_dst [expr {[info exists ::env(FPGA_BITSTREAM)] \
                   ? $::env(FPGA_BITSTREAM) \
                   : "$project_root/bitstream/kestrel_bram.bit"}]
file mkdir [file dirname $bit_dst]
if {[file exists $bit_src]} {
    file copy -force $bit_src $bit_dst
    puts "\nBitstream: $bit_dst"
} else {
    puts stderr "ERROR: bitstream not found at $bit_src"
    exit 1
}
puts "Build complete. Reports in $rpt_dir/"
