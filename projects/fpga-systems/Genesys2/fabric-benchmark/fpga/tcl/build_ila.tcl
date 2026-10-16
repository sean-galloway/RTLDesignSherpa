#==============================================================================
# build_ila.tcl -- fabric benchmark ILA debug build (any leg)
#==============================================================================
# The normal leg build plus one ILA on aclk watching S0: the AXI4 port between
# the fabric and the DDR3 controller (fb_litedram), taken from the top-level
# ddr_* nets, which exist whatever controller sits behind them. It splits "the
# fabric never issued it" from "the controller never answered".
#
# Published next to the normal bitstream as <flow>_ila.{bit,ltx}.
# Capture: tcl/capture_ila.tcl. Usage: make -C build-<leg> bitstream-ila
#==============================================================================
set script_dir [file dirname [file normalize [info script]]]
source "$script_dir/create_project.tcl"

puts "\n--- Synthesis ---"
reset_run synth_1
launch_runs synth_1 -jobs 8
wait_on_run synth_1
if {[get_property PROGRESS [get_runs synth_1]] != "100%"} {
    puts stderr "ERROR: synthesis failed."
    exit 1
}
open_run synth_1 -name synth_1

set dbg_clk [get_nets -of_objects [get_pins u_ep_mmcm/CLKIN1]]
puts "ILA clock net: $dbg_clk"

set probes {}
foreach p {arvalid arready araddr arlen arid rvalid rready rlast rid rresp
           awvalid awready awaddr awlen wvalid wready wlast bvalid bready bresp} {
    set nets [get_nets -quiet "ddr_${p}"]
    if {[llength $nets] == 0} { set nets [get_nets -quiet "ddr_${p}\[*\]"] }
    if {[llength $nets] == 0} { puts "NOTE: no top-level net ddr_$p"; continue }
    lappend probes "ddr_$p" [lsort -dictionary $nets]
}
foreach p {ddr_init_done ddr_init_error ddr_pll_locked} {
    set nets [get_nets -quiet $p]
    if {[llength $nets] == 0} { puts "NOTE: no top-level net $p"; continue }
    lappend probes $p $nets
}

set depth 8192
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
connect_debug_port u_ila_0/clk $dbg_clk

set idx 0
foreach {name nets} $probes {
    if {$idx == 0} { set port u_ila_0/probe0 } else {
        create_debug_port u_ila_0 probe; set port u_ila_0/probe$idx }
    set_property port_width [llength $nets] [get_debug_ports $port]
    set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports $port]
    connect_debug_port $port [get_nets $nets]
    puts [format "  probe%-3d %-18s %3d bits" $idx $name [llength $nets]]
    incr idx
}
puts "ILA: $idx probes, depth $depth"

puts "\n--- Implementation (with ILA) ---"
opt_design
place_design -directive ExtraTimingOpt
phys_opt_design -directive AggressiveExplore
route_design -directive Explore
phys_opt_design -directive AggressiveExplore
set rpt_dir "$project_root/reports"
file mkdir $rpt_dir
report_timing_summary -file "$rpt_dir/timing_summary_ila.txt"
set wns [get_property SLACK [get_timing_paths -max_paths 1 -nworst 1 -setup]]
puts "WNS: $wns"
if {$wns < 0} { puts stderr "ERROR: ILA build does not meet timing (WNS $wns)."; exit 1 }

set bit_dst [expr {[info exists ::env(FPGA_BITSTREAM)] \
                   ? [file normalize $::env(FPGA_BITSTREAM)] \
                   : "$project_root/bitstream/${project_name}_genesys2.bit"}]
# make/fpga_flow.mk ILA_BITSTREAM: <bitstream dir>/<flow>_ila.bit
set ila_base "[file dirname $bit_dst]/${project_name}_ila"
file mkdir [file dirname $bit_dst]
write_bitstream    -force "${ila_base}.bit"
write_debug_probes -force "${ila_base}.ltx"
puts "\nILA bitstream: ${ila_base}.bit"
puts "ILA probes:    ${ila_base}.ltx"
