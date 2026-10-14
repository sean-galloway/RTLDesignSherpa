#==============================================================================
# build_ila.tcl -- amber pair-rig Genesys2 ILA debug build.
#
# Synthesizes amber_pair_genesys2_top with AMBER_ILA_DBG defined (the harness
# then marks its observation taps with mark_debug), instruments them with a
# single u_ila_0 (depth 4096 on aclk), implements, and publishes
# amber_bringup_ila.bit + .ltx next to the normal bitstream.
#
# The taps (rtl/amber_pair_harness.sv, AMBER_DBG_NET) mirror the uart tb's
# probe_* outputs 1:1, so a board capture lines up with the sim golden
# reference (golden_probes.vcd):
#   host_*   bridge host_32b R (+ AR)  rdata/rresp/rlast on the R beat
#   fub_*    host_adapter R channel
#   cvr_*    harness_csr_adapter converter R
#   sla_*    harness CSR slave (s0)
#   ci0/ci1_* injector req/rsp/done/busy/err
# Synthesis renames unmarked handshake nets, so the RTL mark_debug (not
# post-synth name matching) is what keeps these connectable -- same pattern
# as rapids build_ila.tcl.
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

# Turn the harness observation taps on; the perf/normal build never defines
# this, so it carries no mark_debug nets (rapids RAPIDS_CHAR_ILA pattern).
set src_fs [get_filesets sources_1]
set defs [get_property verilog_define $src_fs]
lappend defs AMBER_ILA_DBG=1
set_property verilog_define $defs $src_fs
puts "verilog_define: $defs"

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

# ---- Collect MARK_DEBUG nets, grouped by basename (bus bits -> one probe) ----
set marked [get_nets -hier -filter {MARK_DEBUG}]
puts "marked nets: [llength $marked]"
array set grp {}
foreach n $marked {
    set base [lindex [split $n /] end]
    # Named-generate scopes render as "genblock.sig" in flattened names.
    set base [lindex [split $base .] end]
    if {[regexp {^(.+)\[(\d+)\]$} $base -> b bit]} { set base $b }
    if {![info exists grp($base)]} { set grp($base) {} }
    lappend grp($base) $n
}

# Golden-reference probe order (matches golden_probes.vcd column order; the
# harness-level taps keep their RTL names -- s0_r*/ci0_*/ci1_* -- which the
# golden aliases map onto: s0_rvalid==sla_rvalid, ci0_req_valid==ci0_req_v, ...).
set order {host_arvalid host_arready host_rvalid host_rready host_rdata \
           host_rresp host_rlast fub_rvalid fub_rready cvr_rvalid cvr_rlast \
           s0_rvalid s0_rready \
           ci0_req_valid ci0_req_ready ci0_rsp_valid ci0_rsp_ready \
           ci0_done ci0_busy ci0_err \
           ci1_req_valid ci1_req_ready ci1_rsp_valid ci1_rsp_ready \
           ci1_done ci1_busy ci1_err \
           ub_state ub_rx_valid ub_fub_arv ub_fub_arr ub_m_arv ub_m_arr \
           ub_fub_rv ub_fub_rr}

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
    if {![info exists grp($name)]} {
        puts stderr "ERROR: MARK_DEBUG net '$name' not found post-synth."
        puts stderr "marked bases: [lsort [array names grp]]"
        exit 1
    }
    set nets [lsort $grp($name)]
    if {$idx == 0} { set port u_ila_0/probe0 } else {
        create_debug_port u_ila_0 probe; set port u_ila_0/probe$idx }
    set_property port_width [llength $nets] [get_debug_ports $port]
    set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports $port]
    connect_debug_port $port [get_nets $nets]
    puts [format "  probe%-3d %-12s %3d bits  %s" $idx $name [llength $nets] [lindex $nets 0]]
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
