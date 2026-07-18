#==============================================================================
# build_ila.tcl — build ddr2_char WITH an ILA on the marked DFI-boundary nets.
#
# Instruments the on-silicon debug surface: an ILA (on aclk = sys 75 MHz)
# captures exactly what pumice drives into the a7ddrphy (command + wrdata +
# enables) and what the PHY returns (rddata / rddata_valid), plus idelay_rdy.
# The (* mark_debug *) attributes in ddr2_char_top.sv select the nets; this
# script builds the debug core from them and runs impl in-memory.
#
# Usage (via `make bitstream-ila`, which sets the env like `make bitstream`):
#   vivado -mode batch -source tcl/build_ila.tcl
# Output bitstream (with ILA): build/vivado_project/.../ddr2_char_top.bit
#   copied to bitstream/ddr2_char_ila.bit + the .ltx probe file alongside.
#==============================================================================

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]

puts "========================================================================"
puts "DDR2 Characterization — ILA debug build"
puts "========================================================================"

source "$script_dir/create_project.tcl"

# ---- Enable the aligner's param-gated deskew debug probes (ILA build only) ----
# +define+DESKEW_DEBUG lights up the (* mark_debug *) nets inside
# pumice_dfi_rd_aligner (deskew value reaching the aligner + raw vs deskewed
# word). The release build (build_all.tcl) never sets this, so it stays clean.
set _dbg_fs [get_filesets sources_1]
set _dbg_def [get_property verilog_define $_dbg_fs]
lappend _dbg_def "DESKEW_DEBUG"
set_property verilog_define $_dbg_def $_dbg_fs
puts "ILA build: +define+DESKEW_DEBUG (aligner deskew probes enabled)"

# ---- Synthesis (keep MARK_DEBUG nets) ----
puts "\n--- Synthesis ---"
reset_run synth_1
launch_runs synth_1 -jobs 4
wait_on_run synth_1
if {[get_property PROGRESS [get_runs synth_1]] != "100%"} {
    puts stderr "ERROR: synthesis failed."; exit 1
}

# ---- Insert the ILA on the synthesized netlist ----
puts "\n--- ILA insertion ---"
open_run synth_1 -name synth_1

# Clock net for the ILA: the sys-domain net that clocks the DFI-boundary regs.
# aclk = w_sys (BUFG output) in ddr2_char_top. Resolve robustly.
set dbg_clk ""
foreach cand {aclk w_sys} {
    set n [get_nets -quiet -hier -filter "NAME =~ *$cand"]
    if {[llength $n] > 0} { set dbg_clk [lindex $n 0]; break }
}
if {$dbg_clk eq ""} {
    # fall back to the clock net of a marked flop
    set dbg_clk [get_nets -quiet -hier -filter {NAME =~ *w_sys*}]
    set dbg_clk [lindex $dbg_clk 0]
}
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

# Collect ALL MARK_DEBUG nets and group them into buses by base name (strip
# the [N] bit suffix), preserving bit order. Robust vs get_nets bracket-glob
# quirks (a literal "name[*]" is a Tcl char-class, not a bus wildcard).
set marked [get_nets -hier -filter {MARK_DEBUG}]
puts "marked nets: [llength $marked]"
set order {}
array set grp {}
foreach n $marked {
    if {[regexp {^(.+)\[(\d+)\]$} $n -> base bit]} {
        # bus bit
    } else {
        set base $n; set bit 0
    }
    if {![info exists grp($base)]} { lappend order $base; set grp($base) {} }
    lappend grp($base) [list $bit $n]
}
set idx 0
foreach base $order {
    set pairs [lsort -integer -index 0 $grp($base)]
    set nets {}
    foreach p $pairs { lappend nets [lindex $p 1] }
    if {$idx == 0} {
        set port u_ila_0/probe0
    } else {
        create_debug_port u_ila_0 probe
        set port u_ila_0/probe$idx
    }
    set_property port_width [llength $nets] [get_debug_ports $port]
    set_property PROBE_TYPE DATA_AND_TRIGGER [get_debug_ports $port]
    connect_debug_port $port [get_nets $nets]
    puts [format "  probe%-2d  %-26s  %3d bits" $idx $base [llength $nets]]
    incr idx
}
puts "ILA: $idx probes, depth $depth"
if {$idx == 0} { puts stderr "ERROR: no MARK_DEBUG nets found — nothing to probe."; exit 1 }

# ---- Implementation in-memory (ILA is in the current netlist) ----
puts "\n--- Implementation (in-memory, with ILA) ---"
opt_design
place_design -directive ExtraTimingOpt
phys_opt_design -directive AggressiveExplore
route_design -directive Explore
phys_opt_design -directive AggressiveExplore

file mkdir "$project_root/reports"
report_timing_summary -file "$project_root/reports/timing_summary_ila.txt"
puts "WNS: [get_property SLACK [get_timing_paths -max_paths 1 -nworst 1 -setup]]"

# ---- Bitstream + debug probes (.ltx) ----
set impl_dir "$project_root/build/vivado_project/ddr2_char.runs/impl_1"
file mkdir $impl_dir
write_bitstream -force "$impl_dir/ddr2_char_top.bit"
write_debug_probes -force "$impl_dir/ddr2_char_top.ltx"

file mkdir "$project_root/bitstream"
file copy -force "$impl_dir/ddr2_char_top.bit" "$project_root/bitstream/ddr2_char_ila.bit"
file copy -force "$impl_dir/ddr2_char_top.ltx" "$project_root/bitstream/ddr2_char_ila.ltx"
puts "\nILA bitstream: $project_root/bitstream/ddr2_char_ila.bit"
puts "ILA probes:    $project_root/bitstream/ddr2_char_ila.ltx"
puts "========================================================================"
