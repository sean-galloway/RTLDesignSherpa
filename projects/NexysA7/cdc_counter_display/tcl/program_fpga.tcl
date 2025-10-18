#==============================================================================
# FPGA Programming Script
#==============================================================================
# Project: CDC Counter Display
# Purpose: Program Nexys A7 FPGA with generated bitstream
#==============================================================================

set script_dir [file dirname [file normalize [info script]]]
set project_root "$script_dir/.."
set bitstream_file "$project_root/cdc_counter_display.bit"

puts "========================================================================"
puts "Programming Nexys A7 FPGA"
puts "========================================================================"

## Check if bitstream exists
if {![file exists $bitstream_file]} {
    puts "ERROR: Bitstream not found at $bitstream_file"
    puts "Please run build first: vivado -mode batch -source $script_dir/build_all.tcl"
    exit 1
}

## Open hardware manager
open_hw_manager

## Connect to hardware server
puts "\nConnecting to hardware server..."
connect_hw_server -allow_non_jtag

## Get available hardware targets
set hw_targets [get_hw_targets]
if {[llength $hw_targets] == 0} {
    puts "ERROR: No hardware targets found!"
    puts "Please check:"
    puts "  1. Nexys A7 is powered on"
    puts "  2. USB cable is connected"
    puts "  3. Digilent cable drivers are installed"
    exit 1
}

## Open first target (usually localhost:3121/xilinx_tcf/Digilent/...)
puts "\nOpening hardware target..."
set hw_target [lindex $hw_targets 0]
current_hw_target $hw_target
open_hw_target

## Get hardware device (XC7A100T)
set hw_device [lindex [get_hw_devices] 0]
if {$hw_device == ""} {
    puts "ERROR: No hardware device found on target!"
    exit 1
}

current_hw_device $hw_device
puts "  Found device: $hw_device"

## Set bitstream file
set_property PROGRAM.FILE $bitstream_file $hw_device

## Program device
puts "\nProgramming device..."
puts "  Bitstream: $bitstream_file"

program_hw_devices $hw_device

## Verify programming
refresh_hw_device $hw_device

puts "\n========================================================================"
puts "Programming completed successfully!"
puts "========================================================================"
puts ""
puts "The design is now running on your Nexys A7 board!"
puts ""
puts "Usage Instructions:"
puts "  - Press center button (BTNC) to increment counter"
puts "  - Counter value displays on rightmost 2 digits (00-FF hex)"
puts "  - Press up button (BTNU) to reset counter to 00"
puts "  - LED0: Button clock domain heartbeat (blinks slowly)"
puts "  - LED1: Display clock domain heartbeat (blinks faster)"
puts ""
puts "Educational Notes:"
puts "  - This demonstrates safe clock domain crossing (CDC)"
puts "  - Button domain runs at 10 Hz"
puts "  - Display domain runs at 1 kHz"
puts "  - Pulse-based CDC handshake ensures data integrity"
puts "========================================================================"

## Close hardware manager
close_hw_manager
