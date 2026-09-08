#==============================================================================
# program_fpga_demo.tcl — Flash cdc_demo.bit to the Nexys A7
#==============================================================================
# Invoked via `make program-demo`.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]
set bitfile      "$project_root/cdc_demo.bit"

if {![file exists $bitfile]} {
    puts "ERROR: $bitfile not found. Run `make build-demo` first."
    exit 1
}

puts "Opening hardware target..."
open_hw_manager
connect_hw_server
open_hw_target

set hw_dev [lindex [get_hw_devices xc7a100t_0] 0]
current_hw_device $hw_dev
refresh_hw_device $hw_dev

set_property PROGRAM.FILE $bitfile $hw_dev
puts "Programming: $bitfile"
program_hw_devices $hw_dev
refresh_hw_device $hw_dev

close_hw_target
disconnect_hw_server
close_hw_manager

puts ""
puts "================================================================"
puts "FPGA programmed with $bitfile"
puts "Try the host script:"
puts "  python3 host/run_cdc_demo.py --port /dev/ttyUSB1 smoke"
puts "================================================================"
