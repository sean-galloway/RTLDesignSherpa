#==============================================================================
# capture_ila.tcl — program the rapids_char ILA bitstream, ARM the ILA on the
# first write AW handshake, then drive one SINK run over UART (CHANNEL_RESET
# disabled) so the write phase is captured. Dumps the B->commit->FIFO accounting
# waveform to CSV to see exactly where a committed beat escapes.
#
# Usage:  RAPIDS_CHAR_JTAG_SERIAL=200300B818A0 vivado -mode batch -source tcl/capture_ila.tcl [-tclargs <out.csv> <beats>]
#==============================================================================
set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]
set repo_root    [file normalize "$project_root/../../../.."]
set bit "$project_root/bitstream/rapids_char_ila.bit"
set ltx "$project_root/bitstream/rapids_char_ila.ltx"
set out   [expr {$argc >= 1 ? [lindex $argv 0] : "$project_root/reports/ila_commit_trace.csv"}]
set beats [expr {$argc >= 2 ? [lindex $argv 1] : 16}]
# No hardcoded default. This carried a GENESYS 2 serial while the flow's own
# Makefile defaults to the Nexys, so running it bare aimed at whichever board
# that string happened to match. FPGA_JTAG_SERIAL is the one override name;
# RAPIDS_CHAR_JTAG_SERIAL is still read so existing shells keep working.
set serial ""
foreach v {FPGA_JTAG_SERIAL RAPIDS_CHAR_JTAG_SERIAL} {
    if {[info exists ::env($v)] && $::env($v) ne ""} { set serial $::env($v); break }
}
if {$serial eq ""} {
    puts stderr "ERROR: set FPGA_JTAG_SERIAL (see 'make board-info' for this board's serial)."
    exit 1
}
set uart   [expr {[info exists ::env(RAPIDS_CHAR_UART)] ? $::env(RAPIDS_CHAR_UART) : "/dev/ttyUSB1"}]

open_hw_manager
connect_hw_server -allow_non_jtag
# A serial identifies a CABLE, not a scan chain. An FT2232 exposes two channels
# and the registered serial is a PREFIX of both, so first-match returns the one
# with no devices -- "No devices detected on target ...", which reads as board
# missing. Match, sort longest-first, then take the candidate that HAS a device.
# A failed open also poisons the sibling, hence the reconnect.
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

# Reproduce the wedge FIRST (drive the sink run to completion), leaving the
# commit accounting frozen in its stuck state, THEN immediate-trigger to snapshot
# the frozen values (r_write_beats_to_commit stuck value + FIFO state + last
# commit). Reliable — no trigger-probe-name lookup needed.
puts "Driving SINK run (beats=$beats) over $uart to reproduce the wedge ..."
set st [catch {exec bash -c "cd $repo_root && source ./env_python >/dev/null 2>&1 && python3 projects/fpga-systems/Genesys2/rapids_characterization/flows-rapids-beats/host/run_sink_once.py $uart $beats"} msg]
puts "sink run output: $msg"

run_hw_ila -trigger_now $ila
wait_on_hw_ila -timeout 30 $ila
upload_hw_ila_data $ila
write_hw_ila_data -csv_file -force $out [current_hw_ila_data]
puts "ILA commit trace written: $out"
close_hw_manager
