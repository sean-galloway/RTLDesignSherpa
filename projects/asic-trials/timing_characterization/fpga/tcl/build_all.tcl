#==============================================================================
# build_all.tcl — synth + impl + bitstream for char_top_fpga
#==============================================================================
# Usage: REPO_ROOT=... vivado -mode batch -source build_all.tcl
# Driven by `make bitstream`.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]
set project_file "$project_root/build/vivado_project/timing_char.xpr"

puts "========================================================================"
puts "Timing Characterization — Full FPGA Build"
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

# Utilization report immediately after synth - resource-fit check.
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
puts "\n--- Reports ---"
open_run impl_1
set rpt_dir "$project_root/reports"
report_utilization      -file "$rpt_dir/utilization_impl.txt"
report_timing_summary   -file "$rpt_dir/timing_summary.txt"
report_timing -delay_type max -max_paths 50 -sort_by group \
    -file "$rpt_dir/timing_worst.txt"
report_power            -file "$rpt_dir/power.txt"

# ---- Stash the bitstream ----
file mkdir "$project_root/bitstream"
set bit_src "$project_root/build/vivado_project/timing_char.runs/impl_1/char_top_fpga.bit"
set bit_dst "$project_root/bitstream/timing_char.bit"
if {[file exists $bit_src]} {
    file copy -force $bit_src $bit_dst
    puts "Bitstream copied -> $bit_dst"
} else {
    puts stderr "WARN: bitstream not found at $bit_src"
}

puts "\n========================================================================"
puts "Done.  Reports under $rpt_dir"
puts "========================================================================"
