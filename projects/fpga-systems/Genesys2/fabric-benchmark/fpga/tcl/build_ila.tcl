#==============================================================================
# build_ila.tcl -- fabric benchmark ILA debug build (any leg)
#==============================================================================
# The normal leg build plus one ILA on aclk (MIG's ui_clk) watching S0: MIG's
# AXI4 slave port, taken at MIG's own pins so synthesis renaming cannot hide
# it, and MIG's native app interface underneath its AXI shim. That pair splits
# "the AXI request never became a DRAM command" from "the command ran and the
# data never came back".
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

set dbg_clk [get_nets -of_objects [get_pins u_mig/ui_clk]]
puts "ILA clock net: $dbg_clk"

# Probe name -> nets. MIG AXI pins first (exact), then app-interface nets
# inside the IP (patterns; a miss shrinks the view and is reported).
set probes {}
foreach p {s_axi_arvalid s_axi_arready s_axi_araddr s_axi_arlen s_axi_arid
           s_axi_rvalid s_axi_rready s_axi_rlast s_axi_rid s_axi_rresp
           s_axi_awvalid s_axi_awready s_axi_wvalid s_axi_wready
           s_axi_bvalid s_axi_bready init_calib_complete} {
    set pins [get_pins -quiet "u_mig/${p}*"]
    if {$p in {s_axi_arvalid s_axi_arready s_axi_rvalid s_axi_rready s_axi_rlast
               s_axi_awvalid s_axi_awready s_axi_wvalid s_axi_wready
               s_axi_bvalid s_axi_bready init_calib_complete}} {
        set pins [get_pins -quiet "u_mig/$p"]
    }
    set nets [get_nets -quiet -of_objects $pins]
    if {[llength $nets] == 0} { puts "NOTE: no net on u_mig/$p"; continue }
    lappend probes $p [lsort $nets]
}
foreach {name pat} {
    app_en            "*u_mig/*app_en"
    app_rdy           "*u_mig/*app_rdy"
    app_cmd           "*u_mig/*app_cmd[*]"
    app_rd_data_valid "*u_mig/*app_rd_data_valid"
    app_rd_data_end   "*u_mig/*app_rd_data_end"
    app_wdf_wren      "*u_mig/*app_wdf_wren"
    app_wdf_rdy       "*u_mig/*app_wdf_rdy"
} {
    set nets [get_nets -quiet -hier -filter "NAME =~ $pat"]
    if {[llength $nets] == 0} { puts "NOTE: pattern found no nets: $pat"; continue }
    # The same signal is visible at several hierarchy levels; keep the
    # shortest-named copy (one probe per signal).
    set best {}
    set bestlen 100000
    foreach n $nets {
        set base [regsub {\[\d+\]$} $n {}]
        set l [string length $base]
        if {$l < $bestlen} { set bestlen $l; set best $base }
    }
    set sel {}
    foreach n $nets { if {[regsub {\[\d+\]$} $n {}] eq $best} { lappend sel $n } }
    puts "  $name <- $best ([llength $sel] bit(s))"
    lappend probes $name [lsort -dictionary $sel]
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
