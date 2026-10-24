# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# capture_ila.tcl -- program the ILA build (tcl/build_ila.tcl), arm the ILA
# on the host's first AXI-lite command (uart_awvalid or uart_arvalid), drive
# one host probe over the UART, and write the capture as CSV.
#
#   make tcl-capture_ila ARGS="[out.csv] [uart]"    (FPGA_JTAG_SERIAL from the registry)
#
# If the host command never reaches the AXI-lite side, the ILA is forced after
# the wait so the capture still shows the idle state of every handshake.

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]
set repo_root    [file normalize "$project_root/../../../../.."]   ;# fpga -> stream -> dma-ip -> Genesys2 -> fpga-systems -> projects -> repo
set flow         [expr {[info exists ::env(FPGA_FLOW)] ? $::env(FPGA_FLOW) : "stream_perf"}]
set bit "$project_root/bitstream/${flow}_ila.bit"
set ltx "$project_root/bitstream/${flow}_ila.ltx"
set out  [expr {$argc >= 1 ? [lindex $argv 0] : "$project_root/reports/ila_host_probe.csv"}]
set uart [expr {$argc >= 2 ? [lindex $argv 1] : "/dev/ttyUSB3"}]

set serial ""
foreach v {FPGA_JTAG_SERIAL} {
    if {[info exists ::env($v)] && $::env($v) ne ""} { set serial $::env($v); break }
}
if {$serial eq ""} {
    puts stderr "ERROR: set FPGA_JTAG_SERIAL (see 'make board-info' for this board's serial)."
    exit 1
}

open_hw_manager
connect_hw_server -allow_non_jtag
set matches [lsearch -all -inline -glob [get_hw_targets] "*$serial*"]
if {[llength $matches] == 0} {
    puts stderr "ERROR: no JTAG target matching '$serial' in: [get_hw_targets]"
    exit 1
}
set tgt ""
foreach cand $matches {
    if {[catch {current_hw_target $cand; open_hw_target}]} {
        catch {close_hw_target}
        continue
    }
    if {[llength [get_hw_devices]] > 0} { set tgt $cand; break }
    catch {close_hw_target}
}
if {$tgt eq ""} { puts stderr "ERROR: no device behind '$serial'."; exit 1 }
current_hw_device [lindex [get_hw_devices] 0]
refresh_hw_device -update_hw_probes false [current_hw_device]
set_property PROGRAM.FILE $bit [current_hw_device]
set_property PROBES.FILE  $ltx [current_hw_device]
program_hw_devices [current_hw_device]
refresh_hw_device [current_hw_device]

set ila [get_hw_ilas -of_objects [current_hw_device]]
puts "probes:"
foreach p [get_hw_probes -of_objects $ila] { puts "  [get_property NAME $p]" }

# Trigger: any DUT-side master starting a transaction (nothing should move
# before the host has configured a channel), or the host's commands; the
# window is centred so the lead-up is visible too
set_property CONTROL.TRIGGER_POSITION 2048 $ila
set_property CONTROL.TRIGGER_CONDITION OR $ila
set trig_pats [expr {[info exists ::env(ILA_TRIG)] ? $::env(ILA_TRIG) : "*desc_arvalid* *rd_arvalid* *wr_awvalid* *mon_awvalid*"}]
foreach pat $trig_pats {
    set p [get_hw_probes -quiet -of_objects $ila -filter "NAME =~ $pat"]
    if {[llength $p] > 0} {
        set_property TRIGGER_COMPARE_VALUE eq1'b1 [lindex $p 0]
        puts "trigger: [get_property NAME [lindex $p 0]] == 1"
    }
}
run_hw_ila $ila
after 500

puts "Driving one host probe over $uart ..."
set st [catch {exec bash -c "cd $repo_root && source ./env_python >/dev/null 2>&1 && FPGA_BOARD=genesys2 timeout 60 python3 projects/fpga-systems/Genesys2/dma-ip/stream/build-perf/host/host_status.py --port $uart 2>&1 | head -12"} msg]
puts "host output:\n$msg"

if {[catch {wait_on_hw_ila -timeout 20 $ila} err]} {
    puts "no trigger within 20 s ($err) -- forcing a capture of the idle state"
    run_hw_ila -trigger_now $ila
    wait_on_hw_ila -timeout 10 $ila
}
upload_hw_ila_data $ila
file mkdir [file dirname $out]
write_hw_ila_data -csv_file -force $out [current_hw_ila_data]
puts "ILA capture written: $out"
close_hw_manager
