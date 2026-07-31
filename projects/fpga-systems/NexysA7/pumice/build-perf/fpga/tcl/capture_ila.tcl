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
# Project root: the Makefile exports FPGA_PROJECT_ROOT so the layout is
# explicit rather than inferred from where this script happens to sit.
# Falls back to the old script-relative guess for direct invocation.
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]
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

# Trigger source: "wr" (default) triggers on the WRITE burst (wrdata_en != 0) with
# an EARLY trigger position so the post-trigger window captures the write burst +
# command columns (and the following reads) — to check writes land beats at the
# right DRAM columns with the bl-scaling split. "rd" triggers on rddata_valid.
# "ref" triggers on a REFRESH command (ras_n AND cas_n both asserted — the unique
# DDR2 REF encoding vs ACT=ras-only / RD|WR=cas-only), positioned MID-buffer so the
# window shows the ACT before + the RD after the refresh — to see a refresh
# colliding with an in-flight read (ACT->REF->RD).
set trig [expr {$argc >= 2 ? [lindex $argv 1] : "wr"}]
if {$trig eq "ref"} {
    # Compound trigger: BOTH ras_n and cas_n asserted (!= all-ones) => REF only.
    # Basic ILA ANDs all probes that have a compare value set (global AND).
    set pr [get_hw_probes -of_objects $ila *w_dfi_ras_n*]
    set pc [get_hw_probes -of_objects $ila *w_dfi_cas_n*]
    set wr [get_property WIDTH $pr]
    set wc [get_property WIDTH $pc]
    set onr [format %X [expr {(1 << $wr) - 1}]]
    set onc [format %X [expr {(1 << $wc) - 1}]]
    set_property TRIGGER_COMPARE_VALUE "neq${wr}'h${onr}" $pr
    set_property TRIGGER_COMPARE_VALUE "neq${wc}'h${onc}" $pc
    # Qualify with read activity so we only trigger on a refresh that lands WHILE
    # reads are in flight (rddata_en != 0) — i.e. the ACT->REF->RD collision, not
    # a refresh in an idle gap. Global-AND of all three compares.
    if {![info exists env(CAP_REF_QUAL)] || $env(CAP_REF_QUAL) ne "0"} {
        set pe [get_hw_probes -of_objects $ila *w_dfi_rddata_en*]
        set we2 [get_property WIDTH $pe]
        set_property TRIGGER_COMPARE_VALUE "neq${we2}'h0" $pe
        puts "ILA armed (trigger: REF & rddata_en != 0 = refresh during a read)."
    } else {
        puts "ILA armed (trigger: REF = ras_n & cas_n both asserted). Waiting for a refresh ..."
    }
    set_property CONTROL.TRIGGER_POSITION [expr {[get_property CONTROL.DATA_DEPTH $ila] / 2}] $ila
} elseif {$trig eq "rd"} {
    set p [get_hw_probes -of_objects $ila *w_dfi_rddata_valid*]
    set_property CONTROL.TRIGGER_POSITION [expr {[get_property CONTROL.DATA_DEPTH $ila] - 512}] $ila
    set _pw [get_property WIDTH $p]
    set_property TRIGGER_COMPARE_VALUE "neq${_pw}'h0" $p
    puts "ILA armed (trigger: dfi_rddata_valid != 0). Waiting for a UART read ..."
} elseif {$trig eq "lmr"} {
    # Load Mode Register (MRS): ras_n AND cas_n AND we_n ALL asserted. Pumice
    # issues commands on phase 0 only, so during an MRS phase 0 has all three low
    # (bus != all-ones) while every other DDR2 command leaves >=1 of the three
    # high -> unique to MRS. Global-AND of the three "neq all-ones" compares.
    # Early trigger position so the full init MRS chain (EMRS*, MRS0+DLL, MRS0,
    # OCD) is captured post-trigger. Fire it by re-running init (soft_reset).
    foreach pn {*w_dfi_ras_n* *w_dfi_cas_n* *w_dfi_we_n*} {
        set p [get_hw_probes -of_objects $ila $pn]
        set w [get_property WIDTH $p]
        set on [format %X [expr {(1 << $w) - 1}]]
        set_property TRIGGER_COMPARE_VALUE "neq${w}'h${on}" $p
    }
    set_property CONTROL.TRIGGER_POSITION 256 $ila
    puts "ILA armed (trigger: LMR = ras_n & cas_n & we_n all asserted = MRS). Waiting for init ..."
} else {
    set p [get_hw_probes -of_objects $ila *w_dfi_wrdata_en*]
    set_property CONTROL.TRIGGER_POSITION 512 $ila
    set _pw [get_property WIDTH $p]
    set_property TRIGGER_COMPARE_VALUE "neq${_pw}'h0" $p
    puts "ILA armed (trigger: dfi_wrdata_en != 0). Waiting for a UART write ..."
}
run_hw_ila $ila
# Block up to ~60 s for the trigger (the orchestrator drives a read meanwhile).
wait_on_hw_ila -timeout 60 $ila
upload_hw_ila_data $ila
write_hw_ila_data -csv_file -force $out [current_hw_ila_data]
puts "ILA capture written: $out"
close_hw_manager
