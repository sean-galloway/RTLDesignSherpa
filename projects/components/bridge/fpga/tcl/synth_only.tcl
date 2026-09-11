#==============================================================================
# synth_only.tcl -- out-of-context synth + place + route of ONE generated bridge
#==============================================================================
# Invoked by `make synth` (projects/components/bridge/fpga/Makefile), which
# exports BRIDGE_TOP, BRIDGE_PART, BRIDGE_CLK_NS, FPGA_FILELIST and
# FPGA_PROJECT_ROOT. Non-project batch flow: the whole run is one process and
# leaves nothing but reports behind.
#
# What it measures, and how to read it (HAS 6.4):
#   - clocks: every port ending in `aclk` gets a clock of BRIDGE_CLK_NS; a
#     bridge with CDC slave ports therefore gets one clock per domain, declared
#     asynchronous to each other, exactly as a system would constrain it.
#   - I/O: inputs arrive and outputs must be valid 30% of the period into the
#     cycle (a registered neighbour on both sides). That is the standard
#     out-of-context convention, not a bridge property; the register-to-register
#     WNS is reported separately and is the number that belongs to the bridge.
#   - Fmax in summary.csv is derived from the register-to-register slack at the
#     constrained period (1000 / (T - WNS)); it is an estimate at THIS period,
#     and a tighter constraint can move it either way. Re-run at the target.
#==============================================================================
set script_dir   [file dirname [file normalize [info script]]]
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]
foreach var {BRIDGE_TOP BRIDGE_PART BRIDGE_CLK_NS FPGA_FILELIST REPO_ROOT} {
    if {![info exists ::env($var)]} {
        puts stderr "ERROR: $var is not set -- run via `make synth` in projects/components/bridge/fpga"
        exit 1
    }
}
set top    $::env(BRIDGE_TOP)
set part   $::env(BRIDGE_PART)
set clk_ns [expr {double($::env(BRIDGE_CLK_NS))}]
set rpt    "$project_root/reports/${top}__${part}"
file mkdir $rpt
set t0 [clock seconds]
set io_ns [expr {0.3 * $clk_ns}]

puts "========================================================================"
puts "bridge OOC characterization: $top on $part at $clk_ns ns"
puts "reports: $rpt"
puts "========================================================================"

# ---- sources -----------------------------------------------------------------
source "$script_dir/filelist_utils.tcl"
set fl [file normalize $::env(FPGA_FILELIST)]
if {![file exists $fl]} { puts stderr "ERROR: filelist not found: $fl"; exit 1 }
lassign [filelist::flatten $fl] srcs incdirs defines
set filtered {}
foreach s $srcs {
    if {[string match "*verilator_xilinx_stubs.sv" $s]} { continue }
    if {![file exists $s]} { puts stderr "ERROR: source not found: $s"; exit 1 }
    lappend filtered $s
}
puts "[llength $filtered] sources, [llength $incdirs] include dirs, [llength $defines] defines"

# XILINX selects the distributed-RAM attributes in bridge_cam.sv; SYNTHESIS is
# implicit in Vivado and drops the `ifndef SYNTHESIS` checkers in the xbar.
set vdefs [list XILINX=1]
foreach d $defines { lappend vdefs $d }

# ---- synth (out of context) ----------------------------------------------------
file mkdir "$project_root/build"
set dcp "$project_root/build/${top}__${part}_routed.dcp"
set reuse [expr {[info exists ::env(BRIDGE_REUSE_DCP)] && $::env(BRIDGE_REUSE_DCP) ne "" && [file exists $dcp]}]
if {$reuse} {
    # The routed checkpoint lets the report stage be re-run alone instead of
    # paying for synth+place+route again.
    puts "reusing routed checkpoint $dcp"
    open_checkpoint $dcp
}
if {!$reuse} {
read_verilog -sv $filtered
synth_design -top $top -part $part -mode out_of_context \
    -include_dirs $incdirs -verilog_define $vdefs \
    -flatten_hierarchy rebuilt
report_utilization -file "$rpt/utilization_synth.txt"

# ---- constraints ---------------------------------------------------------------
# One clock per `*aclk` port: the fabric clock, plus one per CDC slave port.
set clk_ports [get_ports -quiet -regexp {.*aclk$}]
if {[llength $clk_ports] == 0} { puts stderr "ERROR: no *aclk port on $top"; exit 1 }
set clk_names {}
foreach p $clk_ports {
    set n [get_property NAME $p]
    create_clock -name $n -period $clk_ns $p
    lappend clk_names $n
}
if {[llength $clk_names] > 1} {
    # Independent domains -- the crossing inside the CDC adapter is an async
    # FIFO with synchronised Gray pointers, and the paths across it are
    # covered by the standard CDC report below rather than by setup analysis.
    set groups {}
    foreach n $clk_names { lappend groups -group [get_clocks $n] }
    set_clock_groups -asynchronous {*}$groups
    puts "clocks: $clk_names (declared asynchronous)"
} else {
    puts "clock: $clk_names"
}
set data_in  [filter [all_inputs]  "NAME !~ *aclk && NAME !~ *aresetn"]
set data_out [all_outputs]
set main_clk [get_clocks [lindex $clk_names 0]]
foreach n $clk_names {
    # ports carrying a CDC slave's name are timed against that slave's clock
    if {$n eq "aclk"} { continue }
    set stem [string range $n 0 end-5]
    set sin  [filter $data_in  "NAME =~ ${stem}_*"]
    set sout [filter $data_out "NAME =~ ${stem}_*"]
    if {[llength $sin]}  { set_input_delay  -clock [get_clocks $n] $io_ns $sin }
    if {[llength $sout]} { set_output_delay -clock [get_clocks $n] $io_ns $sout }
    set data_in  [filter $data_in  "NAME !~ ${stem}_*"]
    set data_out [filter $data_out "NAME !~ ${stem}_*"]
}
if {[llength $data_in]}  { set_input_delay  -clock $main_clk $io_ns $data_in }
if {[llength $data_out]} { set_output_delay -clock $main_clk $io_ns $data_out }
set_false_path -from [filter [all_inputs] "NAME =~ *aresetn"]

# ---- implement -----------------------------------------------------------------
opt_design
place_design
route_design
write_checkpoint -force $dcp
}
set clk_names {}
foreach c [get_clocks] { lappend clk_names [get_property NAME $c] }

# ---- reports -------------------------------------------------------------------
report_utilization    -file "$rpt/utilization_impl.txt"
report_utilization    -hierarchical -hierarchical_depth 1 -file "$rpt/utilization_hier.txt"
report_timing_summary -file "$rpt/timing_summary.txt" -max_paths 10
report_timing -setup -max_paths 20 -nworst 1 -sort_by slack -input_pins -file "$rpt/timing_worst.txt"
report_timing -setup -from [all_registers] -to [all_registers] -max_paths 20 -nworst 1 -sort_by slack \
    -input_pins -file "$rpt/timing_worst_reg2reg.txt"
report_clock_interaction -file "$rpt/clock_interaction.txt"
report_cdc -file "$rpt/cdc.txt"
report_route_status -file "$rpt/route_status.txt"

# ---- one-line summary ----------------------------------------------------------
proc util_num {text label} {
    if {[regexp -line "^\\|\\s*${label}\\*?\\s*\\|\\s*(\\d+)" $text _ n]} { return $n }
    return "?"
}
set ut   [read [set fh [open "$rpt/utilization_impl.txt"]]]; close $fh
set luts [util_num $ut {Slice LUTs}]
set ffs  [util_num $ut {Slice Registers}]
set bram [util_num $ut {Block RAM Tile}]
set dsp  [util_num $ut {DSPs}]
set p_all [get_timing_paths -setup -max_paths 1]
set wns   [expr {[llength $p_all] ? [get_property SLACK $p_all] : "inf"}]
set p_r2r [get_timing_paths -setup -from [all_registers] -to [all_registers] -max_paths 1]
set wns_r2r [expr {[llength $p_r2r] ? [get_property SLACK $p_r2r] : "inf"}]
set fmax  [expr {$wns_r2r eq "inf" ? "n/a" : [format "%.1f" [expr {1000.0 / ($clk_ns - $wns_r2r)}]]}]
set levels [expr {[llength $p_r2r] ? [get_property LOGIC_LEVELS $p_r2r] : 0}]
set unrouted [regexp -line {There are (\d+) unrouted nets} [report_route_status -return_string] _ nn]
set nets_bad [expr {$unrouted ? $nn : 0}]
set secs [expr {[clock seconds] - $t0}]
set line [format "%s,%s,%.3f,%s,%s,%s,%s,%.3f,%.3f,%s,%d,%d,%d" \
    $top $part $clk_ns $luts $ffs $bram $dsp $wns $wns_r2r $fmax $levels $nets_bad $secs]
set csv "$project_root/reports/summary.csv"
if {![file exists $csv]} {
    set fh [open $csv w]
    puts $fh "bridge,part,clk_ns,luts,ffs,bram_tiles,dsps,wns_ns,wns_reg2reg_ns,fmax_reg2reg_mhz,worst_logic_levels,unrouted_nets,seconds"
    close $fh
}
set fh [open $csv a]; puts $fh $line; close $fh
set fh [open "$rpt/summary.txt" w]
puts $fh "bridge=$top part=$part clk_ns=$clk_ns"
puts $fh "luts=$luts ffs=$ffs bram_tiles=$bram dsps=$dsp"
puts $fh "wns_ns=$wns wns_reg2reg_ns=$wns_r2r fmax_reg2reg_mhz=$fmax worst_logic_levels=$levels unrouted_nets=$nets_bad"
puts $fh "clocks=$clk_names io_delay_ns=$io_ns seconds=$secs"
close $fh
puts "========================================================================"
puts "SUMMARY $line"
puts "reports in $rpt ; appended to $csv"
puts "========================================================================"
