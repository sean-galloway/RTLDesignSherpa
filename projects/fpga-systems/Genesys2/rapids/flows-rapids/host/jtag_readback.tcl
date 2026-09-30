#==============================================================================
# jtag_readback.tcl -- list the JTAG targets/devices the hw_server can see
#==============================================================================
# Read-only: opens the hardware manager and prints one line per target and per
# device. Never programs anything. Parsed by board_guard.py.
#
#   JTAG_TARGET <target name>
#   JTAG_DEVICE <target name> <device name> <part> <idcode>
#
# A property that does not exist prints n/a rather than failing the readback.
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
