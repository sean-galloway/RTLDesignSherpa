#==============================================================================
# program_fpga.tcl -- program the Genesys 2 over JTAG with the monitor build
#==============================================================================
# Usage: invoked by `make program`.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]

set bit_file    "$project_root/bitstream/stream_mon_genesys2.bit"
set want_serial "200300B818A0"     ;# Genesys 2 (shared JTAG chain)

if {![file exists $bit_file]} {
    puts stderr "ERROR: $bit_file not found -- run `make bitstream` first."
    exit 1
}

puts "Opening hw_server..."
open_hw_manager
connect_hw_server

# Pin to the Genesys 2 serial so JTAG flash + UART land on the same board.
# Override with STREAM_CHAR_JTAG_SERIAL / RAPIDS_CHAR_JTAG_SERIAL if needed.
if {[info exists ::env(RAPIDS_CHAR_JTAG_SERIAL)]} { set want_serial $::env(RAPIDS_CHAR_JTAG_SERIAL) }
if {[info exists ::env(STREAM_CHAR_JTAG_SERIAL)]} { set want_serial $::env(STREAM_CHAR_JTAG_SERIAL) }
set tgt [lsearch -inline -glob [get_hw_targets] "*$want_serial*"]
if {$tgt eq ""} {
    puts stderr "ERROR: no JTAG target matching '$want_serial' in: [get_hw_targets]"
    exit 1
}
puts "Opening hw_target $tgt (serial $want_serial)"
open_hw_target $tgt

set dev [lindex [get_hw_devices] 0]     ;# xc7k325t_0 on the Genesys 2
current_hw_device $dev
refresh_hw_device [current_hw_device]

set_property PROGRAM.FILE $bit_file $dev
puts "Programming $dev with $bit_file"
program_hw_devices $dev
refresh_hw_device $dev

close_hw_target
close_hw_manager
puts "Program complete."
