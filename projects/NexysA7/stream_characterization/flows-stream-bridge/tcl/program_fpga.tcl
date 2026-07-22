#==============================================================================
# program_fpga.tcl — program the Nexys A7 over JTAG with the freshest build
#==============================================================================
# Usage: vivado -mode batch -source program_fpga.tcl
# Invoked by `make program`.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]

# Board-aware bitstream + JTAG serial defaults (BOARD env: nexys|genesys2).
# Nexys A7 = 210292B7D46F, Genesys 2 = 200300B818A0 (shared JTAG chain).
set bit_file    "$project_root/bitstream/stream_char.bit"
set want_serial "210292B7D46F"
if {[info exists ::env(BOARD)] && $::env(BOARD) eq "genesys2"} {
    set bit_file    "$project_root/bitstream/stream_char_genesys2.bit"
    set want_serial "200300B818A0"
}

if {![file exists $bit_file]} {
    puts stderr "ERROR: $bit_file not found — run `make bitstream` first."
    exit 1
}

puts "Opening hw_server..."
open_hw_manager
connect_hw_server

# Pin to a specific board serial so that, when multiple Digilent boards are
# attached, the JTAG flash and the UART characterization land on the SAME
# board. Override with STREAM_CHAR_JTAG_SERIAL (or the shared-chain selector
# RAPIDS_CHAR_JTAG_SERIAL) if needed.
if {[info exists ::env(RAPIDS_CHAR_JTAG_SERIAL)]} {
    set want_serial $::env(RAPIDS_CHAR_JTAG_SERIAL)
}
if {[info exists ::env(STREAM_CHAR_JTAG_SERIAL)]} {
    set want_serial $::env(STREAM_CHAR_JTAG_SERIAL)
}
set tgt [lsearch -inline -glob [get_hw_targets] "*$want_serial*"]
if {$tgt eq ""} {
    puts stderr "ERROR: no JTAG target matching '$want_serial' in: [get_hw_targets]"
    exit 1
}
puts "Opening hw_target $tgt (serial $want_serial)"
open_hw_target $tgt

# Auto-select the device on the chosen target (xc7a100t_0 on the Nexys,
# xc7k325t_0 on the Genesys 2). Assumes a single FPGA on the opened target.
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
