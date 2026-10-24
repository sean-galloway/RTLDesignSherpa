# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# build_ila.tcl -- the perf/mon build plus an ILA on the handshakes
# stream_harness.sv marks under STREAM_CHAR_ILA (host AXI-lite, STREAM APB,
# the three DUT masters, the monitor writer, the unit reset). Run through
# `make bitstream-ila [STREAM_G=1 ...]`: create_project.tcl reads the same
# environment the plain build does, so the ILA build is the SAME design.
#
# Output: fpga/bitstream/<flow>_ila.bit + .ltx (ILA_BITSTREAM in fpga_flow.mk).
# Capture with tcl/capture_ila.tcl (`make tcl-capture_ila`).
#
# Pattern: projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids/tcl/build_ila.tcl

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]
set flow         [expr {[info exists ::env(FPGA_FLOW)] ? $::env(FPGA_FLOW) : "stream_perf"}]

puts "========================================================================"
puts "STREAM harness -- ILA debug build (STREAM_CHAR_ILA handshakes)"
puts "========================================================================"

source "$script_dir/create_project.tcl"

set src_fs [get_filesets sources_1]
set defs [get_property verilog_define $src_fs]
lappend defs STREAM_CHAR_ILA
set_property verilog_define $defs $src_fs
puts "verilog_define: $defs"

puts "\n--- Synthesis (keep MARK_DEBUG nets) ---"
reset_run synth_1
launch_runs synth_1 -jobs 4
wait_on_run synth_1
if {[get_property PROGRESS [get_runs synth_1]] != "100%"} {
    puts stderr "ERROR: synthesis failed."; exit 1
}

puts "\n--- ILA insertion ---"
open_run synth_1 -name synth_1

set dbg_clk ""
foreach cand {aclk clk_unbuf} {
    set n [get_nets -quiet -hier -filter "NAME =~ $cand"]
    if {[llength $n] == 0} { set n [get_nets -quiet -hier -filter "NAME =~ *$cand"] }
    if {[llength $n] > 0} { set dbg_clk [lindex $n 0]; break }
}
if {$dbg_clk eq ""} { puts stderr "ERROR: no clock net found."; exit 1 }
puts "ILA clock net: $dbg_clk"

set depth 4096
create_debug_core u_ila_0 ila
set_property C_DATA_DEPTH        $depth [get_debug_cores u_ila_0]
set_property C_TRIGIN_EN         false  [get_debug_cores u_ila_0]
set_property C_TRIGOUT_EN        false  [get_debug_cores u_ila_0]
set_property C_ADV_TRIGGER       false  [get_debug_cores u_ila_0]
set_property C_INPUT_PIPE_STAGES 1      [get_debug_cores u_ila_0]
set_property C_EN_STRG_QUAL      false  [get_debug_cores u_ila_0]
set_property ALL_PROBE_SAME_MU     true [get_debug_cores u_ila_0]
set_property ALL_PROBE_SAME_MU_CNT 1    [get_debug_cores u_ila_0]
set_property port_width 1 [get_debug_ports u_ila_0/clk]
connect_debug_port u_ila_0/clk [get_nets $dbg_clk]

# One probe per marked net (or per marked vector), in a stable order
set marked [get_nets -hier -filter {MARK_DEBUG}]
puts "marked nets: [llength $marked]"
set order {}
array set grp {}
foreach n $marked {
    if {[regexp {^(.+)\[(\d+)\]$} $n -> base bit]} {
    } else { set base $n; set bit 0 }
    if {![info exists grp($base)]} { lappend order $base; set grp($base) {} }
    lappend grp($base) [list $bit $n]
}
set idx 0
foreach base $order {
    set pairs [lsort -integer -index 0 $grp($base)]
    set nets {}
    foreach p $pairs { lappend nets [lindex $p 1] }
    if {$idx == 0} { set port u_ila_0/probe0 } else {
        create_debug_port u_ila_0 probe; set port u_ila_0/probe$idx }
    set_property port_width [llength $nets] [get_debug_ports $port]
    set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports $port]
    connect_debug_port $port [get_nets $nets]
    puts [format "  probe%-3d %-70s %3d bits" $idx $base [llength $nets]]
    incr idx
}
puts "ILA: $idx probes, depth $depth"
if {$idx == 0} { puts stderr "ERROR: no MARK_DEBUG nets found."; exit 1 }

puts "\n--- Implementation (in-memory, with ILA) ---"
opt_design
place_design -directive ExtraTimingOpt
phys_opt_design -directive AggressiveExplore
route_design -directive Explore
phys_opt_design -directive AggressiveExplore

file mkdir "$project_root/reports"
report_timing_summary -file "$project_root/reports/timing_summary_ila.txt"
puts "WNS: [get_property SLACK [get_timing_paths -max_paths 1 -nworst 1 -setup]]"

file mkdir "$project_root/bitstream"
set bit "$project_root/bitstream/${flow}_ila.bit"
set ltx "$project_root/bitstream/${flow}_ila.ltx"
write_bitstream    -force $bit
write_debug_probes -force $ltx
puts "\nILA bitstream: $bit"
puts "ILA probes:    $ltx"
puts "========================================================================"
