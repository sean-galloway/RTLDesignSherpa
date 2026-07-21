#==============================================================================
# program_fpga.tcl — program the Nexys A7 over JTAG with the freshest build
#==============================================================================
# Usage: vivado -mode batch -source program_fpga.tcl
# Invoked by `make program`.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]
# Default to the plain bitstream; DDR2_CHAR_BIT selects another (e.g. the ILA
# superset, which is the same design plus DFI-boundary probes — one bitstream
# that both runs the host programs and captures the DFI boundary).
set bit_file     "$project_root/bitstream/ddr2_char.bit"
if {[info exists ::env(DDR2_CHAR_BIT)]} {
    set bit_file $::env(DDR2_CHAR_BIT)
}

if {![file exists $bit_file]} {
    puts stderr "ERROR: $bit_file not found — run `make bitstream` first."
    exit 1
}

puts "Opening hw_server..."
open_hw_manager
connect_hw_server

# Pin to a specific board serial so multi-board bench setups can't misroute
# the flash. Override with the DDR2_CHAR_JTAG_SERIAL env var if needed.
# If unset, we take the first target Vivado enumerates.
set want_serial ""
if {[info exists ::env(DDR2_CHAR_JTAG_SERIAL)]} {
    set want_serial $::env(DDR2_CHAR_JTAG_SERIAL)
}
if {$want_serial ne ""} {
    set tgt [lsearch -inline -glob [get_hw_targets] "*$want_serial*"]
    if {$tgt eq ""} {
        puts stderr "ERROR: no JTAG target matching '$want_serial' in: [get_hw_targets]"
        exit 1
    }
    puts "Opening hw_target $tgt (serial $want_serial)"
} else {
    set tgt [lindex [get_hw_targets] 0]
    if {$tgt eq ""} {
        puts stderr "ERROR: no JTAG targets found"
        exit 1
    }
    puts "Opening first hw_target: $tgt"
    puts "  (set DDR2_CHAR_JTAG_SERIAL to pin to a specific board)"
}
open_hw_target $tgt

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
