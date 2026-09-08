#==============================================================================
# build_demo.tcl — Synth + Impl + Bitstream for cdc_demo_top
#==============================================================================
# Invoked via `make build-demo`.
#==============================================================================

set script_dir [file dirname [file normalize [info script]]]

# Create project (force-recreates the demo project subdir)
source "$script_dir/create_project_demo.tcl"

puts ""
puts "----------------------------------------------------------------"
puts "Launching synthesis..."
puts "----------------------------------------------------------------"
reset_run synth_1
launch_runs synth_1 -jobs 4
wait_on_run synth_1
if {[get_property PROGRESS [get_runs synth_1]] != "100%"} {
    puts "ERROR: synth_1 did not complete cleanly."
    exit 1
}

puts ""
puts "----------------------------------------------------------------"
puts "Launching implementation + bitstream..."
puts "----------------------------------------------------------------"
reset_run impl_1
launch_runs impl_1 -to_step write_bitstream -jobs 4
wait_on_run impl_1
if {[get_property PROGRESS [get_runs impl_1]] != "100%"} {
    puts "ERROR: impl_1 did not complete cleanly."
    exit 1
}

# Copy bitstream to project root + reports out for convenience
set project_root [file normalize "$script_dir/.."]
set bitsrc "$project_root/vivado_project_demo/cdc_demo.runs/impl_1/cdc_demo_top.bit"
set bitdst "$project_root/cdc_demo.bit"
if {[file exists $bitsrc]} {
    file copy -force $bitsrc $bitdst
    puts "Bitstream copied to: $bitdst"
}

# Drop a few reports next to the project for quick inspection
set reports_dir "$project_root/reports_demo"
file mkdir $reports_dir
foreach report {
    cdc_demo_top_timing_summary_routed.rpt
    cdc_demo_top_utilization_placed.rpt
    cdc_demo_top_drc_routed.rpt
} {
    set src "$project_root/vivado_project_demo/cdc_demo.runs/impl_1/$report"
    if {[file exists $src]} {
        file copy -force $src $reports_dir
    }
}
puts "Reports in: $reports_dir"

puts ""
puts "================================================================"
puts "BUILD-DEMO DONE"
puts "Bitstream: $bitdst"
puts "================================================================"
