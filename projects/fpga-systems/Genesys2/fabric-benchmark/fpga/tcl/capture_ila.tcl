#==============================================================================
# capture_ila.tcl -- program the ILA build, run one DDR3 fill + drain over the
# UART, and capture S0 around the drain's first read request.
#==============================================================================
# The fill (W1-F2) sends nothing on S0's AR channel -- descriptors come from
# desc_ram at S1 -- so the trigger, S0 ARVALID rising, is the drain's first
# DDR3 read. Pre-trigger 1/8 of the window, so the capture is mostly what MIG
# does after the request.
#
# Run through the flow, which holds the board lock and sets FPGA_JTAG_SERIAL:
#   make -C build-<leg> tcl-capture_ila
# The host steps are bin/fb_ila_drive.py, started from the shell once the ILA
# is armed (this tcl waits up to 5 minutes for the trigger).
# Output: <project_root>/reports/ila_s0.csv
#==============================================================================
set script_dir   [file dirname [file normalize [info script]]]
set area         [file normalize "$script_dir/../.."]
set project_root [file normalize $::env(FPGA_PROJECT_ROOT)]
set flow         [expr {[info exists ::env(FLOW)] ? $::env(FLOW) : "fb_a"}]
set bit "$project_root/bitstream/${flow}_ila.bit"
set ltx "$project_root/bitstream/${flow}_ila.ltx"
foreach f [list $bit $ltx] {
    if {![file exists $f]} { puts stderr "ERROR: $f not found -- run 'make bitstream-ila' first."; exit 1 }
}
set serial [expr {[info exists ::env(FPGA_JTAG_SERIAL)] ? $::env(FPGA_JTAG_SERIAL) : ""}]
if {$serial eq ""} { puts stderr "ERROR: FPGA_JTAG_SERIAL is not set (run via make tcl-capture_ila)."; exit 1 }
set out  "$project_root/reports/ila_s0.csv"

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
# The debug hub runs on ui_clk, which MIG starts only once its MMCM locks:
# a refresh straight after programming finds no ILA. Retry for a few seconds.
set ila ""
for {set i 0} {$i < 10 && $ila eq ""} {incr i} {
    after 1000
    refresh_hw_device [current_hw_device]
    set ila [lindex [get_hw_ilas -quiet -of_objects [current_hw_device]] 0]
}
if {$ila eq ""} { puts stderr "ERROR: no ILA found after programming (is ui_clk running?)"; exit 1 }

set depth [get_property CONTROL.DATA_DEPTH $ila]
set_property CONTROL.TRIGGER_POSITION [expr {$depth / 8}] $ila
set_property CONTROL.TRIGGER_CONDITION AND $ila
# Probe names are the connected net names; take the S0 ARVALID one by pattern.
set trig [lindex [get_hw_probes -of_objects $ila -filter {NAME =~ "*arvalid*"}] 0]
if {$trig eq ""} { puts stderr "ERROR: no *arvalid* probe in [get_hw_probes -of_objects $ila]"; exit 1 }
puts "trigger probe: $trig"
set_property TRIGGER_COMPARE_VALUE eq1'bR $trig
run_hw_ila $ila
puts "ILA armed (S0 ARVALID rising, depth $depth)"

# The host program runs OUTSIDE Vivado: Vivado's own PYTHONHOME breaks the
# repo venv in a child process. Start it from the shell once this prints
# "ILA armed" -- bin/fb_ila_drive.py --port <uart> -- within the wait below.
if {[catch {wait_on_hw_ila -timeout 5 $ila} err]} {
    puts stderr "ERROR: ILA never triggered -- no read request reached S0 ($err)"
    exit 1
}
upload_hw_ila_data $ila
file mkdir [file dirname $out]
write_hw_ila_data -csv_file -force $out [current_hw_ila_data]
puts "ILA capture: $out"
