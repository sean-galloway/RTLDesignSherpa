#==============================================================================
# program_fpga.tcl — flash Nexys A7-100T via JTAG
#==============================================================================
# Assumes the board is plugged in via USB and the Vivado hardware server is
# reachable on localhost:3121.  Reuses the most recent bitstream from
# fpga/bitstream/timing_char.bit.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]
set bit_file     "$project_root/bitstream/timing_char.bit"

if {![file exists $bit_file]} {
    puts stderr "ERROR: no bitstream at $bit_file - run 'make bitstream' first."
    exit 1
}

open_hw_manager
connect_hw_server -url localhost:3121
current_hw_target [get_hw_targets */xilinx_tcf/*]
open_hw_target

# Find the Artix-7 device on the chain.
current_hw_device [get_hw_devices xc7a100t_0]
refresh_hw_device [current_hw_device]
set_property PROGRAM.FILE $bit_file [current_hw_device]
program_hw_devices [current_hw_device]

close_hw_target
close_hw_manager
puts "Programmed $bit_file"
