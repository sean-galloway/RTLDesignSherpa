#==============================================================================
# program_fpga.tcl -- program ANY board in this lab over JTAG
#==============================================================================
# The one copy. Seven near-identical per-flow copies used to each hardcode a
# bitstream path, a JTAG serial, and their own env-var name to override it; this
# script knows none of those and is handed everything:
#
#   FPGA_BITSTREAM    absolute path to the .bit (REQUIRED)
#   FPGA_JTAG_SERIAL  JTAG target serial to pin (optional; else sole target)
#   FPGA_BOARD        board name, for the log line only (optional)
#
# Normally invoked through fpga/bin/fpga_board.py, which fills those in from the
# board registry. Directly:
#   FPGA_BITSTREAM=/path/to.bit vivado -mode batch -notrace -source program_fpga.tcl
#==============================================================================

if {![info exists ::env(FPGA_BITSTREAM)]} {
    puts stderr "ERROR: FPGA_BITSTREAM is not set."
    exit 1
}
set bit_file $::env(FPGA_BITSTREAM)

if {![file exists $bit_file]} {
    puts stderr "ERROR: $bit_file not found -- run 'make bitstream' first."
    exit 1
}

set want_serial ""
if {[info exists ::env(FPGA_JTAG_SERIAL)]} {
    set want_serial $::env(FPGA_JTAG_SERIAL)
}
set board_name "(unnamed)"
if {[info exists ::env(FPGA_BOARD)]} {
    set board_name $::env(FPGA_BOARD)
}

puts "Opening hw_server for $board_name..."
open_hw_manager
connect_hw_server

# Pin to a specific board serial so that, with several Digilent boards on the
# chain, the JTAG flash and the UART campaign land on the SAME board.
set targets [get_hw_targets]
if {$want_serial eq ""} {
    if {[llength $targets] != 1} {
        puts stderr "ERROR: FPGA_JTAG_SERIAL unset and [llength $targets] targets\
                     present: $targets"
        exit 1
    }
    set tgt [lindex $targets 0]
} else {
    # A serial can match MORE THAN ONE target. The FT2232 on these boards
    # exposes two channels and Vivado lists both -- e.g. 200300B818A0 (UART)
    # and 200300B818A0B (JTAG) -- and because the short serial is a PREFIX of
    # the long one, a substring glob matches both. `lsearch -inline` then
    # returns whichever is first, which was the channel with no scan chain:
    #   ERROR: [Labtools 27-2269] No devices detected on target ...
    # That reads as "board missing" when the board is powered and fine.
    #
    # So: match by serial, then pick the candidate that actually has a device.
    # Opening a chainless target fails, hence the catch.
    set matches [lsearch -all -inline -glob $targets "*$want_serial*"]
    if {[llength $matches] == 0} {
        puts stderr "ERROR: no JTAG target matching '$want_serial' in: $targets"
        exit 1
    }
    # LONGEST FIRST. The channels differ by a suffix (...A0 vs ...A0B) and the
    # JTAG one is the more specific name, so trying longest-first usually hits
    # it on the first attempt. That matters because a FAILED open poisons the
    # session for the sibling channel: probing the chainless one first makes
    # the good one report "no scan chain" too. Reconnecting the server between
    # attempts clears that, so the order is an optimisation, not the fix.
    set matches [lsort -command {apply {{a b} {expr {[string length $b] - [string length $a]}}}} $matches]
    set tgt ""
    foreach cand $matches {
        if {[catch {current_hw_target $cand; open_hw_target}]} {
            puts "  $cand -- no scan chain, skipping"
            # Clear the failed-open state before trying the sibling channel.
            catch {close_hw_target}
            catch {disconnect_hw_server}
            connect_hw_server
            continue
        }
        if {[llength [get_hw_devices]] > 0} {
            puts "  $cand -- devices: [get_hw_devices]"
            set tgt $cand
            break
        }
        catch {close_hw_target}
    }
    if {$tgt eq ""} {
        puts stderr "ERROR: '$want_serial' matched [llength $matches] target(s)\
                     but none had a device on the chain: $matches"
        puts stderr "       (board powered on? JTAG cable seated?)"
        exit 1
    }
}
puts "Opening hw_target $tgt"
if {[catch {current_hw_target $tgt; open_hw_target}]} {
    # Already opened by the probe loop above; that is fine.
    current_hw_target $tgt
}

# Auto-select the device on the chosen target (xc7a100t_0 on the Nexys A7,
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
