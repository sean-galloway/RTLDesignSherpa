#==============================================================================
# program_fpga.tcl — program the Nexys A7 over JTAG with the freshest build
#==============================================================================
# Usage: vivado -mode batch -source program_fpga.tcl
# Invoked by `make program`.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]
set bit_file     "$project_root/stream_char.bit"

if {![file exists $bit_file]} {
    puts stderr "ERROR: $bit_file not found — run `make bitstream` first."
    exit 1
}

puts "Opening hw_server..."
open_hw_manager
connect_hw_server
open_hw_target

set dev [lindex [get_hw_devices xc7a100t_0] 0]
current_hw_device $dev
refresh_hw_device [current_hw_device]

set_property PROGRAM.FILE $bit_file $dev
puts "Programming $dev with $bit_file"
program_hw_devices $dev
refresh_hw_device $dev

close_hw_target
close_hw_manager
puts "Program complete."
