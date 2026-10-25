# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# ooc_stream_core.tcl -- stream_core or stream_core_g out of context on the
# Genesys 2 part, in the board's geometry (stream_cfg_pkg: 128-bit data, 32-bit
# addresses, 8 outstanding each way, SRAM_DEPTH 256, shared engines, no AXI
# monitors, EXT addressing built), placed and routed at 100 MHz. The STREAM
# counterpart of rapids MAS Table 5.5.7 / HAS Table 6.4.7 (stream TASK-020).
#
#   OOC_TOP=stream_core|stream_core_g  OOC_CH=8|16  [OOC_PERIOD_NS=10.0]
#   [OOC_OUT=<dir>]  vivado -mode batch -source fpga/tcl/ooc_stream_core.tcl
#
# Output: <area>/reports/ooc/<top>_<ch>ch/<period>ns/{utilization,utilization_hier,
# timing_summary,timing_worst,summary}.txt. Pattern: fabric-benchmark/fpga/tcl/ooc_fabric.tcl.

set script_dir [file dirname [file normalize [info script]]]
set area       [file normalize "$script_dir/../.."]
set rds_root   [expr {[info exists ::env(REPO_ROOT)] ? $::env(REPO_ROOT) \
                      : [string trim [exec git -C $script_dir rev-parse --show-toplevel]]}]
source "$rds_root/make/tcl/filelist_utils.tcl"

foreach v {OOC_TOP OOC_CH} { if {![info exists ::env($v)]} { puts stderr "ERROR: $v is not set"; exit 1 } }
set top    $::env(OOC_TOP)
set nch    $::env(OOC_CH)
set period [expr {[info exists ::env(OOC_PERIOD_NS)] ? $::env(OOC_PERIOD_NS) : 10.0}]
set part   "xc7k325tffg900-2"
set out    [expr {[info exists ::env(OOC_OUT)] ? [file normalize $::env(OOC_OUT)] \
                 : "$area/reports/ooc/${top}_${nch}ch/${period}ns"}]
file mkdir $out

set stream_root "$rds_root/projects/components/dma-ip/stream"
switch -- $top {
    stream_core   { set fl "$stream_root/rtl/filelists/macro/stream_core.f" }
    stream_core_g { set fl "$stream_root/rtl/filelists/macro_g/stream_core_g.f" }
    default { puts stderr "ERROR: OOC_TOP must be stream_core or stream_core_g, got $top"; exit 1 }
}

create_project -in_memory -part $part
set_property target_language Verilog [current_project]
lassign [filelist::flatten $fl] srcs incdirs defines
foreach f $srcs {
    if {![file exists $f]} { puts stderr "ERROR: source not found: $f"; exit 1 }
    if {[string match *.sv $f]} { read_verilog -sv $f } else { read_verilog $f }
}
set_property include_dirs $incdirs [current_fileset]
if {[llength $defines] > 0} { set_property verilog_define $defines [current_fileset] }

# The core's clock port is `clk` (the tops rename it aclk). XDC takes no Tcl
# control flow, so the port is named here; the check after synthesis refuses an
# untimed run (an unconstrained OOC run routes against no period and its WNS
# is blank -- the first attempt did exactly that).
set xdc "$out/ooc_clock.xdc"
set fh [open $xdc w]
puts $fh "create_clock -name core_clk -period $period \[get_ports clk\]"
close $fh
read_xdc -mode out_of_context $xdc

# The board geometry (stream_cfg_pkg + the perf build's exports)
set generics [list NUM_CHANNELS=$nch DATA_WIDTH=128 ADDR_WIDTH=32 SHARED_ENGINES=1 \
                   USE_AXI_MONITORS=0 GEN_MON=0 USE_ROW_COL_MAJOR_ADDRESSING=1 \
                   AR_MAX_OUTSTANDING=8 AW_MAX_OUTSTANDING=8 FIFO_DEPTH=256]
set gargs {}
foreach g $generics { lappend gargs -generic $g }
puts "ooc_stream_core: $top, $nch channels, generics: $generics"
synth_design -top $top -part $part -mode out_of_context {*}$gargs
report_utilization -file "$out/utilization_synth.txt"
if {[llength [get_clocks -quiet]] == 0} { puts stderr "ERROR: no clock constraint took -- untimed run refused"; exit 1 }
opt_design
place_design
phys_opt_design
route_design
report_utilization                -file "$out/utilization.txt"
report_utilization -hierarchical  -file "$out/utilization_hier.txt"
report_timing_summary -max_paths 10 -file "$out/timing_summary.txt"
report_timing -max_paths 20 -nworst 1 -sort_by slack -file "$out/timing_worst.txt"

proc util_row {report name} {
    if {[regexp -line "^\\|\\s+$name\\s+\\|\\s+(\\d+)\\s+\\|" $report -> n]} { return $n }
    return 0
}
set util [report_utilization -return_string]
set wns  [get_property SLACK [get_timing_paths -max_paths 1 -nworst 1 -setup]]
set whs  [get_property SLACK [get_timing_paths -max_paths 1 -nworst 1 -hold]]
set fh [open "$out/summary.txt" w]
puts $fh "top $top"
puts $fh "channels $nch"
puts $fh "part $part"
puts $fh "period_ns $period"
puts $fh "generics $generics"
puts $fh "wns_ns $wns"
puts $fh "whs_ns $whs"
puts $fh "lut [util_row $util {Slice LUTs}]"
puts $fh "lutram [util_row $util {LUT as Distributed RAM}]"
puts $fh "ff [util_row $util {Slice Registers}]"
puts $fh "bram_tile [util_row $util {Block RAM Tile}]"
puts $fh "dsp [util_row $util {DSPs}]"
close $fh
puts "\nooc_stream_core: $top ${nch}ch @ ${period} ns -> $out (WNS $wns ns)"
