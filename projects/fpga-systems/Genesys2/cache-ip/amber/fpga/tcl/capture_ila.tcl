#==============================================================================
# capture_ila.tcl -- program the amber ILA bitstream, drive the wedge over
# UART, then immediate-trigger the ILA to snapshot the frozen state.
#
# Two failure modes are captured in one image:
#   injector -- cycle injectors start but never complete (busy stuck high)
#   read     -- a CSR read over the UART-AXIL bridge never returns
#
# The rapids lesson applies to JTAG serial handling: a serial identifies a
# CABLE, not a scan chain, so match longest-first and open the target that
# actually has a device.
#
# Usage:
#   FPGA_JTAG_SERIAL=200300B818A0 vivado -mode batch -source tcl/capture_ila.tcl \
#       [-tclargs <out.csv> <injector|read|both>]
#==============================================================================
set script_dir   [file dirname [file normalize [info script]]]
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]
set repo_root    [expr {[info exists ::env(REPO_ROOT)] \
                        ? [file normalize $::env(REPO_ROOT)] \
                        : [file normalize "$project_root/../../../../../.."]}]

set out   [expr {$argc >= 1 ? [lindex $argv 0] : "$project_root/reports/ila_trace.csv"}]
set mode  [expr {$argc >= 2 ? [lindex $argv 1] : "both"}]
if {$mode ni {injector read both}} { puts stderr "ERROR: mode must be injector|read|both"; exit 1 }

set bit_dir "$project_root/bitstream"
set bit_base "amber_bringup_ila"
if {[info exists ::env(FPGA_BITSTREAM)] && $::env(FPGA_BITSTREAM) ne ""} {
    set bit_dir  [file dirname [file normalize $::env(FPGA_BITSTREAM)]]
    set bit_base [file rootname [file tail $::env(FPGA_BITSTREAM)]]_ila
}
set bit "$bit_dir/${bit_base}.bit"
set ltx "$bit_dir/${bit_base}.ltx"
foreach f [list $bit $ltx] {
    if {![file exists $f]} { puts stderr "ERROR: $f not found -- run 'make bitstream-ila' first."; exit 1 }
}

set serial ""
foreach v {FPGA_JTAG_SERIAL AMBER_JTAG_SERIAL} {
    if {[info exists ::env($v)] && $::env($v) ne ""} { set serial $::env($v); break }
}
if {$serial eq ""} {
    puts stderr "ERROR: set FPGA_JTAG_SERIAL (see 'make board-info' for this board's serial)."
    exit 1
}
set uart [expr {[info exists ::env(AMBER_UART)] ? $::env(AMBER_UART) : "/dev/ttyUSB1"}]

open_hw_manager
connect_hw_server -allow_non_jtag
set matches [lsearch -all -inline -glob [get_hw_targets] "*$serial*"]
if {[llength $matches] == 0} {
    puts stderr "ERROR: no JTAG target matching '$serial' in: [get_hw_targets]"
    exit 1
}
set matches [lsort -command {apply {{a b} {expr {[string length $b] - [string length $a]}}}} $matches]
set tgt ""
foreach cand $matches {
    if {[catch {current_hw_target $cand; open_hw_target}]} {
        catch {close_hw_target}
        catch {disconnect_hw_server}
        connect_hw_server -allow_non_jtag
        continue
    }
    if {[llength [get_hw_devices]] > 0} { set tgt $cand; break }
    catch {close_hw_target}
}
if {$tgt eq ""} {
    puts stderr "ERROR: '$serial' matched [llength $matches] target(s), none with a device."
    exit 1
}
current_hw_device [lindex [get_hw_devices] 0]
refresh_hw_device -update_hw_probes false [current_hw_device]
set_property PROGRAM.FILE $bit [current_hw_device]
set_property PROBES.FILE  $ltx [current_hw_device]
program_hw_devices [current_hw_device]
refresh_hw_device [current_hw_device]
set ila [get_hw_ilas -of_objects [current_hw_device]]

# Reproduce the wedge first so the stuck state is live in the fabric, THEN
# immediate-trigger to snapshot it -- no trigger-condition setup needed and
# both failure modes persist once wedged.
puts "Driving '$mode' wedge over $uart ..."
set py [file normalize "$project_root/../../host/ila_stim.py"]
set st [catch {exec bash -c "cd $repo_root && source ./env_python >/dev/null 2>&1 && python3 $py $uart $mode"} msg]
puts "stim output: $msg"

run_hw_ila -trigger_now $ila
wait_on_hw_ila -timeout 60 $ila
upload_hw_ila_data $ila
write_hw_ila_data -csv_file -force $out [current_hw_ila_data]
puts "ILA trace written: $out"
close_hw_manager
