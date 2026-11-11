# ooc_cache.tcl -- out-of-context synthesis + place + route of ONE L1 cache
# module, for the cache-only area and Fmax rows of the cache-ip reference
# comparison (cache-ip common-ip TASK-003). Same part, same clock period for
# every cache; the rig builds carry injectors, bridge, UART and memory that
# would blur the comparison.
#
# Env: REPO_ROOT; OOC_TOP (module), OOC_FILELIST (its compile closure, -f
# style, see make/tcl/filelist_utils.tcl), OOC_OUT (report dir),
# OOC_PERIOD_NS (default 10.0), OOC_CLK (clock port, default aclk),
# OOC_GENERICS (optional, "NAME=value NAME=value"), OOC_PART (default the
# Genesys 2 part).
set rds_root [expr {[info exists ::env(REPO_ROOT)] ? $::env(REPO_ROOT) \
                    : [string trim [exec git rev-parse --show-toplevel]]}]
source "$rds_root/make/tcl/filelist_utils.tcl"
foreach v {OOC_TOP OOC_FILELIST OOC_OUT} {
    if {![info exists ::env($v)]} { puts stderr "ERROR: $v is not set"; exit 1 }
}
set top    $::env(OOC_TOP)
set period [expr {[info exists ::env(OOC_PERIOD_NS)] ? $::env(OOC_PERIOD_NS) : 10.0}]
set clk    [expr {[info exists ::env(OOC_CLK)] ? $::env(OOC_CLK) : "aclk"}]
set part   [expr {[info exists ::env(OOC_PART)] ? $::env(OOC_PART) : "xc7k325tffg900-2"}]
set out    [file normalize $::env(OOC_OUT)]
file mkdir $out
create_project -in_memory -part $part
set_property target_language Verilog [current_project]
lassign [filelist::flatten $::env(OOC_FILELIST)] srcs incdirs defines
foreach f $srcs {
    if {![file exists $f]} { puts stderr "ERROR: source not found: $f"; exit 1 }
    if {[string match *.sv $f]} { read_verilog -sv $f } else { read_verilog $f }
}
set_property include_dirs $incdirs [current_fileset]
if {[info exists ::env(OOC_GENERICS)] && $::env(OOC_GENERICS) ne ""} {
    set_property generic $::env(OOC_GENERICS) [current_fileset]
    puts "Generic override: $::env(OOC_GENERICS)"
}
set xdc "$out/ooc_clock.xdc"
set fh [open $xdc w]
puts $fh "create_clock -name $clk -period $period \[get_ports $clk\]"
close $fh
read_xdc -mode out_of_context $xdc
synth_design -top $top -part $part -mode out_of_context
report_utilization -file "$out/utilization_synth.txt"
opt_design
place_design
phys_opt_design
route_design
report_utilization                -file "$out/utilization.txt"
report_utilization -hierarchical  -file "$out/utilization_hier.txt"
report_timing_summary -max_paths 10 -file "$out/timing_summary.txt"
report_timing -max_paths 20 -nworst 1 -sort_by slack -file "$out/timing_worst.txt"
set wns  [get_property SLACK [get_timing_paths -max_paths 1 -nworst 1 -setup]]
set path [get_timing_paths -max_paths 1 -nworst 1 -setup]
set fh [open "$out/summary.txt" w]
puts $fh "top $top"
puts $fh "part $part"
puts $fh "period_ns $period"
puts $fh "wns_ns $wns"
puts $fh "worst_levels [get_property LOGIC_LEVELS $path]"
puts $fh "worst_start [get_property STARTPOINT_PIN $path]"
puts $fh "worst_end [get_property ENDPOINT_PIN $path]"
puts $fh "lut [llength [get_cells -hierarchical -filter {IS_PRIMITIVE && REF_NAME =~ LUT*}]]"
puts $fh "ff [llength [get_cells -hierarchical -filter {IS_PRIMITIVE && REF_NAME =~ FD*}]]"
puts $fh "ramb36 [llength [get_cells -hierarchical -filter {IS_PRIMITIVE && REF_NAME =~ RAMB36*}]]"
puts $fh "ramb18 [llength [get_cells -hierarchical -filter {IS_PRIMITIVE && REF_NAME =~ RAMB18*}]]"
puts $fh "lutram [llength [get_cells -hierarchical -filter {IS_PRIMITIVE && (REF_NAME =~ RAM*M* || REF_NAME =~ RAM*S* || REF_NAME =~ RAM*D*)}]]"
close $fh
puts "OOC DONE $top wns=$wns"
