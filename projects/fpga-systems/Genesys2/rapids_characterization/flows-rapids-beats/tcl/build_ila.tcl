#==============================================================================
# build_ila.tcl — build rapids_char WITH an ILA on the (* mark_debug *) nets in
# scheduler_beats.sv (per-channel r_current_state + read/write/exec complete +
# descriptor_valid). Captures which state each of the 8 sink schedulers is stuck
# in when snk_system_idle fails to re-assert -> isolates the responsible FUB.
#
# Usage (BOARD=genesys2 for the Genesys 2):
#   BOARD=genesys2 vivado -mode batch -source tcl/build_ila.tcl
# Output: bitstream/rapids_char_ila.bit + rapids_char_ila.ltx
#==============================================================================
set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]

puts "========================================================================"
puts "RAPIDS Characterization — ILA debug build (scheduler idle signals)"
puts "========================================================================"
source "$script_dir/create_project.tcl"

puts "\n--- Synthesis (keep MARK_DEBUG nets) ---"
reset_run synth_1
launch_runs synth_1 -jobs 4
wait_on_run synth_1
if {[get_property PROGRESS [get_runs synth_1]] != "100%"} {
    puts stderr "ERROR: synthesis failed."; exit 1
}

puts "\n--- ILA insertion ---"
open_run synth_1 -name synth_1

# DUT clock net (aclk = clk100 BUFG output in the genesys top).
set dbg_clk ""
foreach cand {clk100 aclk clk_100 w_clk100} {
    set n [get_nets -quiet -hier -filter "NAME =~ *$cand"]
    if {[llength $n] > 0} { set dbg_clk [lindex $n 0]; break }
}
if {$dbg_clk eq ""} { puts stderr "ERROR: no clock net found."; exit 1 }
puts "ILA clock net: $dbg_clk"

set depth 2048
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

# Collect ALL MARK_DEBUG nets, group into buses by base name (strip [N] suffix),
# one probe per base. Per-channel signals appear as distinct hier paths -> one
# probe per channel per signal (exactly the 8-way visibility we want).
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

set top_name [get_property top [get_filesets sources_1]]
set impl_dir "$project_root/build/vivado_project/rapids_char.runs/impl_1"
file mkdir $impl_dir
write_bitstream    -force "$impl_dir/${top_name}.bit"
write_debug_probes -force "$impl_dir/${top_name}.ltx"
file mkdir "$project_root/bitstream"
file copy -force "$impl_dir/${top_name}.bit" "$project_root/bitstream/rapids_char_ila.bit"
file copy -force "$impl_dir/${top_name}.ltx" "$project_root/bitstream/rapids_char_ila.ltx"
puts "\nILA bitstream: $project_root/bitstream/rapids_char_ila.bit"
puts "ILA probes:    $project_root/bitstream/rapids_char_ila.ltx"
puts "========================================================================"
