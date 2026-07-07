#==============================================================================
# capture_ila.tcl — program the ILA bitstream, arm the ILA, wait for a read,
# and dump the captured DFI-boundary waveform to a CSV for offline analysis.
#
# Headless capture over the same JTAG used to program. Trigger = the first
# dfi_rddata_valid after arming, positioned near the END of the buffer so the
# preceding WR command + wrdata + the read are all captured. Run a UART read
# (host program) WHILE this is armed so the trigger fires — the companion
# orchestrator capture_read.py arms this in the background then drives the read.
#
# Usage:  vivado -mode batch -source tcl/capture_ila.tcl [-tclargs <out.csv>]
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]
set bit  "$project_root/bitstream/ddr2_char_ila.bit"
set ltx  "$project_root/bitstream/ddr2_char_ila.ltx"
set out  [expr {$argc >= 1 ? [lindex $argv 0] : "$project_root/reports/ila_capture.csv"}]

open_hw_manager
connect_hw_server -allow_non_jtag
open_hw_target
current_hw_device [lindex [get_hw_devices] 0]
refresh_hw_device -update_hw_probes false [current_hw_device]

set_property PROGRAM.FILE $bit [current_hw_device]
set_property PROBES.FILE  $ltx [current_hw_device]
program_hw_devices [current_hw_device]
refresh_hw_device [current_hw_device]

set ila [get_hw_ilas -of_objects [current_hw_device]]

# Trigger on read data returning from the PHY (dfi_rddata_valid != 0). Capture
# with a big pre-trigger window so the preceding write burst + command land in
# the buffer too.
set rdv [get_hw_probes -of_objects $ila *w_dfi_rddata_valid*]
set_property TRIGGER_COMPARE_VALUE {neq2'b00} $rdv
set_property CONTROL.TRIGGER_POSITION [expr {[get_property CONTROL.DATA_DEPTH $ila] - 512}] $ila

puts "ILA armed (trigger: dfi_rddata_valid != 0). Waiting for a UART read ..."
run_hw_ila $ila
# Block up to ~60 s for the trigger (the orchestrator drives a read meanwhile).
wait_on_hw_ila -timeout 60 $ila
upload_hw_ila_data $ila
write_hw_ila_data -csv_file -force $out [current_hw_ila_data]
puts "ILA capture written: $out"
close_hw_manager
