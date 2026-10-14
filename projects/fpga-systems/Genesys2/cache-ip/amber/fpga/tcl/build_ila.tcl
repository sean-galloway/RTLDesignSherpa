#==============================================================================
# build_ila.tcl -- amber pair-rig Genesys2 ILA debug build.
#
# Synthesizes amber_pair_genesys2_top, then instruments the read-path taps and
# the cycle-injector handshake with a single u_ila_0 (depth 4096 on aclk),
# implements, and publishes amber_bringup_ila.bit + .ltx next to the normal
# bitstream. Nets are located by hierarchical name on the synthesized design
# -- no RTL changes, no mark_debug attributes -- and every miss is reported.
#
# Read-path taps mirror dv/amber_pair_harness_uart_tb.sv's probe_* outputs so
# a board capture lines up 1:1 with the sim golden reference
# (dv/tests/local_sim_build/test_amber_pair_harness_uart_func/golden_probes.vcd):
#   u_bridge host_32b R      -> host layer          (rvalid/rready/rlast/rresp/rdata)
#   u_host_adapter fub_axi R -> host-adapter layer  (rvalid/rready)
#   u_harness_csr_adapter    -> CSR-adapter layer   (converter rvalid/rlast)
#   u_harness s0_*           -> harness CSR slave   (rvalid/rready)
# plus host_32b AR (read-issue ordering) and u_ci0/u_ci1 req/rsp/done/busy/err
# (injector non-completion).
#
# Usage: make -C build-bringup bitstream-ila
#==============================================================================
set script_dir   [file dirname [file normalize [info script]]]
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]

puts "========================================================================"
puts "amber pair-rig Genesys2 -- ILA debug build"
puts "========================================================================"
source "$script_dir/create_project.tcl"

# ---- Synthesis ----
puts "\n--- Synthesis ---"
reset_run synth_1
launch_runs synth_1 -jobs 4
wait_on_run synth_1
if {[get_property PROGRESS [get_runs synth_1]] != "100%"} {
    puts stderr "ERROR: synthesis failed."
    exit 1
}
open_run synth_1 -name synth_1

# ---- ILA clock: the 90 MHz harness clock ----
set dbg_clk ""
foreach cand {aclk clk90 clk_90} {
    set n [get_nets -quiet $cand]
    if {[llength $n] > 0} { set dbg_clk [lindex $n 0]; break }
}
if {$dbg_clk eq ""} {
    foreach cand {aclk clk90 clk_90 clk100 clk_100} {
        set n [get_nets -quiet -hier -filter "NAME =~ *$cand"]
        if {[llength $n] > 0} { set dbg_clk [lindex $n 0]; break }
    }
}
if {$dbg_clk eq ""} { puts stderr "ERROR: no ILA clock net found."; exit 1 }
puts "ILA clock net: $dbg_clk"

# ---- Probe nets: anchored-end hierarchical matches, one net each ----
# A miss is fatal (silent ILA without the failing tap is worse than no ILA).
proc pick_net {pattern} {
    set n [get_nets -quiet -hier -filter "NAME =~ $pattern"]
    if {[llength $n] == 0} { puts stderr "ERROR: no net matching $pattern"; exit 1 }
    if {[llength $n] > 1} {
        set n [lsort -command {apply {{a b} {expr {[string length $a] - [string length $b]}}}} $n]
        puts "NOTE: $pattern matched multiple nets; using [lindex $n 0]"
    }
    return [lindex $n 0]
}

# name -> hierarchical pattern (anchored at the end)
array set probes {
    host_arvalid        {*u_bridge/host_32b_arvalid}
    host_arready        {*u_bridge/host_32b_arready}
    host_rvalid         {*u_bridge/host_32b_rvalid}
    host_rready         {*u_bridge/host_32b_rready}
    host_rlast          {*u_bridge/host_32b_rlast}
    host_rresp          {*u_bridge/host_32b_rresp}
    host_rdata          {*u_bridge/host_32b_rdata}
    fub_rvalid          {*u_host_adapter/fub_axi_rvalid}
    fub_rready          {*u_host_adapter/fub_axi_rready}
    cvr_rvalid          {*u_harness_csr_adapter/converter_rvalid}
    cvr_rlast           {*u_harness_csr_adapter/converter_rlast}
    sla_rvalid          {*u_harness/s0_rvalid}
    sla_rready          {*u_harness/s0_rready}
    ci0_req_v           {*u_harness/ci0_req_valid}
    ci0_req_r           {*u_harness/ci0_req_ready}
    ci0_rsp_v           {*u_harness/ci0_rsp_valid}
    ci0_rsp_r           {*u_harness/ci0_rsp_ready}
    ci0_done            {*u_harness/ci0_done}
    ci0_busy            {*u_harness/ci0_busy}
    ci0_err             {*u_harness/ci0_err}
    ci1_req_v           {*u_harness/ci1_req_valid}
    ci1_req_r           {*u_harness/ci1_req_ready}
    ci1_rsp_v           {*u_harness/ci1_rsp_valid}
    ci1_rsp_r           {*u_harness/ci1_rsp_ready}
    ci1_done            {*u_harness/ci1_done}
    ci1_busy            {*u_harness/ci1_busy}
    ci1_err             {*u_harness/ci1_err}
}
set order {host_arvalid host_arready host_rvalid host_rready host_rlast \
           host_rresp host_rdata fub_rvalid fub_rready cvr_rvalid cvr_rlast \
           sla_rvalid sla_rready \
           ci0_req_v ci0_req_r ci0_rsp_v ci0_rsp_r ci0_done ci0_busy ci0_err \
           ci1_req_v ci1_req_r ci1_rsp_v ci1_rsp_r ci1_done ci1_busy ci1_err}

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

set idx 0
foreach name $order {
    set n [pick_net $probes($name)]
    set w [get_property BUS_WIDTH $n]
    if {$idx == 0} { set port u_ila_0/probe0 } else {
        create_debug_port u_ila_0 probe; set port u_ila_0/probe$idx }
    set_property port_width $w [get_debug_ports $port]
    set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports $port]
    connect_debug_port $port [get_nets $n]
    puts [format "  probe%-3d %-12s %3d bits  %s" $idx $name $w $n]
    incr idx
}
puts "ILA: $idx probes, depth $depth"

# ---- Implementation (in-memory; directives mirror build_all.tcl) ----
puts "\n--- Implementation (with ILA) ---"
opt_design
place_design -directive ExtraTimingOpt
phys_opt_design -directive AggressiveExplore
route_design -directive Explore
phys_opt_design -directive AggressiveExplore
file mkdir "$project_root/reports"
report_timing_summary -file "$project_root/reports/timing_summary_ila.txt"
set wns [get_property SLACK [get_timing_paths -max_paths 1 -nworst 1 -setup]]
puts "WNS: $wns"
if {$wns < 0} { puts stderr "ERROR: ILA build does not meet timing." ; exit 1 }

set top_name [get_property top [get_filesets sources_1]]
set impl_dir "$project_root/build/vivado_project/amber.runs/impl_1"
file mkdir $impl_dir
write_bitstream    -force "$impl_dir/${top_name}.bit"
write_debug_probes -force "$impl_dir/${top_name}.ltx"

# Publish next to the normal bitstream, flow naming (amber_bringup_ila.*).
set bit_dir "$project_root/bitstream"
set bit_base "amber_bringup_ila"
if {[info exists ::env(FPGA_BITSTREAM)] && $::env(FPGA_BITSTREAM) ne ""} {
    set bit_dir  [file dirname [file normalize $::env(FPGA_BITSTREAM)]]
    set bit_base [file rootname [file tail $::env(FPGA_BITSTREAM)]]_ila
}
file mkdir $bit_dir
file copy -force "$impl_dir/${top_name}.bit" "$bit_dir/${bit_base}.bit"
file copy -force "$impl_dir/${top_name}.ltx" "$bit_dir/${bit_base}.ltx"
puts "\nILA bitstream: $bit_dir/${bit_base}.bit"
puts "ILA probes:    $bit_dir/${bit_base}.ltx"
puts "========================================================================"
