# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#==============================================================================
# capture_ila.tcl -- program build-xil's ILA bitstream and capture the memory
# links around a stall (make tcl-capture_ila)
#==============================================================================
# Arms on r_ddr_stall, r_bram_stall or r_atg_stall rising (bs_genesys2_xil_top: work pending on a memory
# link and no handshake for 2048 cycles) with all but 512 samples before it,
# then waits ILA_WAIT_S seconds (default 300) for the host to drive traffic --
# run the host from another shell once "ILA armed" prints. Writes
# reports/ila_links.csv. Adapted from the fabric benchmark's MIG capture.
#==============================================================================
set script_dir   [file dirname [file normalize [info script]]]
set area         [file normalize "$script_dir/../.."]
set project_root [file normalize $::env(FPGA_PROJECT_ROOT)]
set flow         [expr {[info exists ::env(FLOW)] ? $::env(FLOW) : "bs_xil"}]
set bit "$project_root/bitstream/${flow}_ila.bit"
set ltx "$project_root/bitstream/${flow}_ila.ltx"
foreach f [list $bit $ltx] {
    if {![file exists $f]} { puts stderr "ERROR: $f not found -- run 'make bitstream-ila' first."; exit 1 }
}
set serial [expr {[info exists ::env(FPGA_JTAG_SERIAL)] ? $::env(FPGA_JTAG_SERIAL) : ""}]
if {$serial eq ""} { puts stderr "ERROR: FPGA_JTAG_SERIAL is not set (run via make tcl-capture_ila)."; exit 1 }
set out  "$project_root/reports/ila_links.csv"

open_hw_manager
connect_hw_server -allow_non_jtag
# A serial names a cable; match longest-first and take the target with a device.
set matches [lsort -command {apply {{a b} {expr {[string length $b] - [string length $a]}}}} \
                 [lsearch -all -inline -glob [get_hw_targets] "*$serial*"]]
set tgt ""
foreach cand $matches {
    if {[catch {current_hw_target $cand; open_hw_target}]} {
        catch {close_hw_target}; catch {disconnect_hw_server}
        connect_hw_server -allow_non_jtag
        continue
    }
    if {[llength [get_hw_devices]] > 0} { set tgt $cand; break }
    catch {close_hw_target}
}
if {$tgt eq ""} { puts stderr "ERROR: no JTAG target with a device for '$serial'."; exit 1 }
current_hw_device [lindex [get_hw_devices] 0]
refresh_hw_device -update_hw_probes false [current_hw_device]
set_property PROGRAM.FILE $bit [current_hw_device]
set_property PROBES.FILE  $ltx [current_hw_device]
program_hw_devices [current_hw_device]
# The debug hub runs on aclk, which LiteDRAM starts only once its PLL locks:
# a refresh straight after programming finds no ILA. Retry for a few seconds.
set ila ""
for {set i 0} {$i < 10 && $ila eq ""} {incr i} {
    after 1000
    refresh_hw_device [current_hw_device]
    set ila [lindex [get_hw_ilas -quiet -of_objects [current_hw_device]] 0]
}
if {$ila eq ""} { puts stderr "ERROR: no ILA found after programming (is ui_clk running?)"; exit 1 }

set depth [get_property CONTROL.DATA_DEPTH $ila]
# most of the window BEFORE the stall flag: the cycles that led into it
set_property CONTROL.TRIGGER_POSITION [expr {$depth - 512}] $ila
set_property CONTROL.TRIGGER_CONDITION OR $ila
foreach l {ddr bram atg} {
    set trig [lindex [get_hw_probes -of_objects $ila -filter "NAME =~ *r_${l}_stall*"] 0]
    if {$trig eq ""} { puts stderr "ERROR: no r_${l}_stall probe"; exit 1 }
    set_property TRIGGER_COMPARE_VALUE eq1'bR $trig
}
run_hw_ila $ila
puts "ILA armed (r_ddr_stall, r_bram_stall or r_atg_stall rising, depth $depth)"
flush stdout
set wait_s [expr {[info exists ::env(ILA_WAIT_S)] ? $::env(ILA_WAIT_S) : 300}]
if {[catch {wait_on_hw_ila -timeout [expr {($wait_s + 59) / 60}] $ila} err]} {
    puts stderr "ERROR: ILA never triggered -- no memory link stalled ($err)"
    exit 1
}
upload_hw_ila_data $ila
file mkdir [file dirname $out]
write_hw_ila_data -csv_file -force $out [current_hw_ila_data]
puts "ILA capture: $out"
