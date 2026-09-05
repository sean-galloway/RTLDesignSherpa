#==============================================================================
# build_all.tcl — synth + impl + bitstream for ddr2_char
#==============================================================================
# Usage:  REPO_ROOT=... CONVERTERS_ROOT=... vivado -mode batch -source \
#         build_all.tcl
# Run via `make bitstream` which sets the env vars and calls this.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
# Project root: the Makefile exports FPGA_PROJECT_ROOT so the layout is
# explicit rather than inferred from where this script happens to sit.
# Falls back to the old script-relative guess for direct invocation.
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]

puts "========================================================================"
puts "DDR2 Characterization — Full Build"
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
# Cheap insurance: same phys-opt levers stream_characterization needed to
# close on the -1 speed grade. If the design has margin to spare, no harm
# done; if we're skating close to 100 MHz, phys_opt closes the last few
# hundred ps by replicating / relocating the marginal endpoints.
puts "\n--- Implementation ---"
set _place_dir [expr {[info exists ::env(PLACE_DIRECTIVE)] ? $::env(PLACE_DIRECTIVE) : "AltSpreadLogic_high"}]
puts "PLACE_DESIGN directive: $_place_dir"
set_property STEPS.PLACE_DESIGN.DIRECTIVE               $_place_dir       [get_runs impl_1]
set_property STEPS.PHYS_OPT_DESIGN.IS_ENABLED           true              [get_runs impl_1]
set_property STEPS.PHYS_OPT_DESIGN.DIRECTIVE            AggressiveExplore [get_runs impl_1]
set _route_dir [expr {[info exists ::env(ROUTE_DIRECTIVE)] ? $::env(ROUTE_DIRECTIVE) : "Explore"}]
puts "ROUTE_DESIGN directive: $_route_dir"
set_property STEPS.ROUTE_DESIGN.DIRECTIVE               $_route_dir       [get_runs impl_1]
set_property STEPS.POST_ROUTE_PHYS_OPT_DESIGN.IS_ENABLED  true            [get_runs impl_1]
set_property STEPS.POST_ROUTE_PHYS_OPT_DESIGN.DIRECTIVE AggressiveExplore [get_runs impl_1]
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
report_utilization         -file "$rpt_dir/utilization_impl.txt"
report_timing_summary      -file "$rpt_dir/timing_summary.txt"
report_timing -sort_by group -max_paths 20 -path_type summary \
                            -file "$rpt_dir/timing_worst.txt"
report_clock_interaction   -file "$rpt_dir/clock_interaction.txt"
report_cdc                 -file "$rpt_dir/cdc.txt"
report_drc                 -file "$rpt_dir/drc.txt"
report_power               -file "$rpt_dir/power.txt"

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

# ---- Copy bitstream into bitstream/ for easy access (committed location) ----
set bit_src "$project_root/build/vivado_project/ddr2_char.runs/impl_1/ddr2_char_top.bit"
set bit_dst "$project_root/bitstream/ddr2_char.bit"
file mkdir "$project_root/bitstream"
if {[file exists $bit_src]} {
    file copy -force $bit_src $bit_dst
    puts "\nBitstream: $bit_dst"
} else {
    puts stderr "WARNING: bitstream not found at $bit_src"
}

puts "========================================================================"
puts "Build complete. Reports in $project_root/reports/"
puts "========================================================================"
