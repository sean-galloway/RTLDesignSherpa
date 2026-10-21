# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#==============================================================================
# build_ila.tcl -- build-xil with an ILA on the memory links (make bitstream-ila)
#==============================================================================
# The same design as build_all.tcl plus one ILA on aclk:
#   ddr, bram     each memory link's handshakes, AWLEN, IDs, WLAST / RLAST,
#                 BRESP / RRESP, its stall detector and outstanding counts
#   masters       the vendor masters' write handshakes
#   checkers      bs_pc_ddr / bs_pc_bram asserted, with each link's AWADDR,
#                 AWSIZE, AWBURST and WSTRB (what the checker judges)
# Capture: fpga/tcl/capture_ila.tcl (make tcl-capture_ila), triggered on
# either stall detector with most of the window before it. It found MIG's
# spurious read return on this board (PRD findings); the method follows the
# fabric benchmark's MIG ILA.
#==============================================================================
set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize $::env(FPGA_PROJECT_ROOT)]
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

# aclk where it enters u_mmcm (the LiteDRAM core is flattened in synthesis)
set dbg_clk [get_nets -of_objects [get_pins u_mmcm/CLKIN1]]
set probes {}
proc bs_probe {name nets} {
    upvar probes probes
    set nets [lsort -dictionary $nets]
    if {[llength $nets] == 0} { puts "NOTE: no nets for $name"; return }
    lappend probes $name $nets
}
foreach l {ddr bram} {
    foreach n {awvalid awready wvalid wready wlast bvalid bready arvalid arready
               rvalid rready rlast} {
        bs_probe ${l}_axi_$n [get_nets -quiet ${l}_axi_$n]
    }
    foreach n {awlen awid bid bresp arid rid rresp} {
        bs_probe ${l}_axi_$n [get_nets -quiet "${l}_axi_${n}[*]"]
    }
    # what the protocol checker judges a write by: address, size, burst, strobes
    foreach n {awaddr awsize awburst wstrb} {
        bs_probe ${l}_axi_$n [get_nets -quiet "${l}_axi_${n}[*]"]
    }
    bs_probe w_pc_${l}_asserted [get_nets -quiet w_pc_${l}_asserted]
    bs_probe r_${l}_stall [get_nets -quiet r_${l}_stall]
    bs_probe r_${l}_wr_out [get_nets -quiet "r_${l}_wr_out[*]"]
    bs_probe r_${l}_rd_out [get_nets -quiet "r_${l}_rd_out[*]"]
}
# the vendor masters' write handshakes (who is writing when it stops)
foreach m {cdma} {
    foreach n {awvalid awready wvalid wready wlast bvalid bready} {
        bs_probe ${m}_axi_$n [get_nets -quiet ${m}_axi_$n]
    }
}
# the traffic generator's whole port, IDs and addresses included
foreach n {awvalid awready wvalid wready wlast bvalid bready arvalid arready
           rvalid rready rlast} {
    bs_probe atg_axi_$n [get_nets -quiet atg_axi_$n]
}
foreach n {awid bid arid rid awlen arlen bresp rresp awaddr araddr} {
    bs_probe atg_axi_$n [get_nets -quiet "atg_axi_${n}[*]"]
}
bs_probe r_atg_stall [get_nets -quiet r_atg_stall]
bs_probe r_atg_wr_out [get_nets -quiet "r_atg_wr_out[*]"]
bs_probe r_atg_rd_out [get_nets -quiet "r_atg_rd_out[*]"]
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
set ila_base "$project_root/bitstream/${project_name}_ila"
file mkdir [file dirname $ila_base]
write_bitstream    -force "${ila_base}.bit"
write_debug_probes -force "${ila_base}.ltx"
puts "\nILA bitstream: ${ila_base}.bit"
