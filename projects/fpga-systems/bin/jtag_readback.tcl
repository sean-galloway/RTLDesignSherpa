#==============================================================================
# jtag_readback.tcl -- list the JTAG targets/devices the hw_server can see
#==============================================================================
# READ-ONLY. Opens the hardware manager, prints one line per target and per
# device, and never programs anything.
#
#   JTAG_TARGET <target name>
#   JTAG_DEVICE <target name> <device name> <part> <idcode>
#
# A property that does not exist prints n/a rather than failing the readback: a
# missing IDCODE is worth reporting, not worth aborting over.
#
# WHY THIS EXISTS. The board lock (tooling TASK-022) prevents two flows driving
# one board. It cannot detect a collision that happened anyway -- a harness
# records the sha256 of the bitstream IT programmed, not what is on the device,
# so a board reprogrammed or re-enumerated mid-run leaves a results file that
# looks entirely valid. A lock prevents; a readback detects. They are
# complements, not alternatives.
#
# This is the SHARED copy, parsed by board.py's parse_readback(). The rapids flow
# has its own copy at Genesys2/rapids/flows-rapids/host/jtag_readback.tcl which
# predates this one; the output format here is deliberately identical so that
# copy can be retired in favour of this without touching its parser. Seven
# copies of program_fpga.tcl is the mistake this tree already made once.
#==============================================================================
open_hw_manager
connect_hw_server
foreach t [get_hw_targets] {
    puts "JTAG_TARGET $t"
    if {[catch {open_hw_target $t} err]} {
        puts "JTAG_TARGET_ERROR $t $err"
        continue
    }
    foreach d [get_hw_devices] {
        set part n/a
        set idcode n/a
        catch {set part [get_property PART $d]}
        catch {set idcode [get_property REGISTER.IDCODE $d]}
        puts "JTAG_DEVICE $t [get_property NAME $d] $part $idcode"
    }
    close_hw_target
}
close_hw_manager
