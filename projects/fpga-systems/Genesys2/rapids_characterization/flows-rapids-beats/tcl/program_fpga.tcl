#==============================================================================
# program_fpga.tcl — program the Nexys A7 over JTAG with the freshest build
#==============================================================================
# Usage: vivado -mode batch -source program_fpga.tcl
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]
set bit_file     "$project_root/bitstream/rapids_char.bit"

if {![file exists $bit_file]} {
    puts stderr "ERROR: $bit_file not found — run the bitstream build first."
    exit 1
}

puts "Opening hw_server..."
open_hw_manager
connect_hw_server

# Pin to a specific board serial when multiple Digilent boards are attached so
# the JTAG flash and the UART campaign (run_characterization.py) land on the
# SAME board. Override with RAPIDS_CHAR_JTAG_SERIAL if needed.
set want_serial "210292B7D46F"
if {[info exists ::env(RAPIDS_CHAR_JTAG_SERIAL)]} {
    set want_serial $::env(RAPIDS_CHAR_JTAG_SERIAL)
}
set tgt [lsearch -inline -glob [get_hw_targets] "*$want_serial*"]
if {$tgt eq ""} {
    puts stderr "ERROR: no JTAG target matching '$want_serial' in: [get_hw_targets]"
    exit 1
}
puts "Opening hw_target $tgt (serial $want_serial)"
open_hw_target $tgt

# Auto-select the device on the chosen target (board-agnostic: xc7a100t_0 on the
# Nexys, xc7k325t_0 on the Genesys 2). Assumes a single FPGA in the JTAG chain.
set dev [lindex [get_hw_devices] 0]
current_hw_device $dev
refresh_hw_device [current_hw_device]

set_property PROGRAM.FILE $bit_file $dev
puts "Programming $dev with $bit_file"
program_hw_devices $dev
refresh_hw_device $dev

close_hw_target
close_hw_manager
puts "Program complete."
