#==============================================================================
# Complete Build Script
#==============================================================================
# Project: CDC Counter Display
# Purpose: Run complete build flow (synthesis → implementation → bitstream)
#==============================================================================

set script_dir [file dirname [file normalize [info script]]]

puts "========================================================================"
puts "Starting Complete Build Flow"
puts "========================================================================"

## Step 1: Create project (if not already open)
if {[catch {current_project}]} {
    puts "\nStep 1: Creating project..."
    source "$script_dir/create_project.tcl"
} else {
    puts "\nStep 1: Project already open"
}

## Step 2: Run synthesis
puts "\nStep 2: Running synthesis..."
reset_run synth_1
launch_runs synth_1 -jobs 4
wait_on_run synth_1

if {[get_property PROGRESS [get_runs synth_1]] != "100%"} {
    puts "ERROR: Synthesis failed!"
    exit 1
}
puts "  Synthesis completed successfully"

## Step 3: Run implementation
puts "\nStep 3: Running implementation..."
launch_runs impl_1 -jobs 4
wait_on_run impl_1

if {[get_property PROGRESS [get_runs impl_1]] != "100%"} {
    puts "ERROR: Implementation failed!"
    exit 1
}
puts "  Implementation completed successfully"

## Step 4: Generate bitstream
puts "\nStep 4: Generating bitstream..."
launch_runs impl_1 -to_step write_bitstream -jobs 4
wait_on_run impl_1

## Step 5: Generate reports
puts "\nStep 5: Generating reports..."
set project_root "$script_dir/.."
file mkdir "$project_root/reports"

open_run impl_1

## Timing report
report_timing_summary -file "$project_root/reports/timing_summary.txt"
report_timing -sort_by group -max_paths 10 -path_type summary -file "$project_root/reports/timing_detailed.txt"

## Utilization report
report_utilization -file "$project_root/reports/utilization.txt"

## Clock interaction report
report_clock_interaction -file "$project_root/reports/clock_interaction.txt"

## CDC report
report_cdc -file "$project_root/reports/cdc_report.txt"

## Power report
report_power -file "$project_root/reports/power.txt"

## DRC report
report_drc -file "$project_root/reports/drc.txt"

puts "\nReports generated in $project_root/reports/"

## Step 6: Copy bitstream to convenient location
puts "\nStep 6: Copying bitstream..."
set bitstream_src "$project_root/vivado_project/cdc_counter_display.runs/impl_1/cdc_counter_display_top.bit"
set bitstream_dst "$project_root/cdc_counter_display.bit"

if {[file exists $bitstream_src]} {
    file copy -force $bitstream_src $bitstream_dst
    puts "  Bitstream copied to: $bitstream_dst"
} else {
    puts "  WARNING: Bitstream not found at $bitstream_src"
}

puts "========================================================================"
puts "Build completed successfully!"
puts "========================================================================"
puts "Bitstream: $bitstream_dst"
puts "Reports:   $project_root/reports/"
puts ""
puts "To program the FPGA:"
puts "  1. Connect Nexys A7 board via USB"
puts "  2. Power on the board"
puts "  3. Run: vivado -mode batch -source $script_dir/program_fpga.tcl"
puts "  Or use Vivado Hardware Manager GUI"
puts "========================================================================"
