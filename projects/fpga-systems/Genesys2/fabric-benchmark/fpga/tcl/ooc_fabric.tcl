#==============================================================================
# ooc_fabric.tcl -- one leg's data fabric, out of context, placed and routed
#==============================================================================
# The fabric under test alone (top fb_data_fabric) on the Genesys 2 part, so the
# three legs are compared on size and timing with nothing else in the device:
#
#   bridge  rtl/filelists/fb_data_fabric_bridge.f
#   xbar    rtl/filelists/fb_data_fabric_xbar.f   (needs XILINX_VIVADO)
#   sc      the fb_sc block design from fpga/tcl/vendor_ip.tcl + its leg wrapper
#
# Environment:
#   FB_LEG        bridge | xbar | sc                     (required)
#   FB_PERIOD_NS  aclk period, default 10.0 (the 100 MHz board target)
#   FB_OUT        report directory, default reports/ooc/<leg>/<period>ns
#   FB_PART       another part instead of the Genesys 2's (e.g. an UltraScale+
#                 one, for Fmax on a faster family); the default report
#                 directory is then reports/ooc/<part>/<leg>/<period>ns, so a
#                 run on another part never overwrites the board-part reports
#                 and bin/parse_ooc.py, which tabulates the board part, skips it
#
# Only register-to-register paths are timed: the ports are unconstrained in an
# OOC run, which is the comparison wanted (the harness registers every port
# that leaves the fabric). Writes utilization (flat + hierarchical), timing
# summary, the worst paths, and summary.txt, which bin/parse_ooc.py reads.
#==============================================================================
set script_dir [file dirname [file normalize [info script]]]
set area       [file normalize "$script_dir/../.."]
set rds_root   [expr {[info exists ::env(REPO_ROOT)] ? $::env(REPO_ROOT) \
                      : [string trim [exec git -C $script_dir rev-parse --show-toplevel]]}]
source "$rds_root/make/tcl/filelist_utils.tcl"
source "$area/rtl/generated/fb_vendor_ip_cfg/fb_vendor_ip_cfg.tcl"

if {![info exists ::env(FB_LEG)]} { puts stderr "ERROR: FB_LEG is not set"; exit 1 }
set leg    $::env(FB_LEG)
set period [expr {[info exists ::env(FB_PERIOD_NS)] ? $::env(FB_PERIOD_NS) : 10.0}]
set board_part [expr {![info exists ::env(FB_PART)] || $::env(FB_PART) eq $FB_PART}]
if {!$board_part} { set FB_PART $::env(FB_PART) }
set out    [expr {[info exists ::env(FB_OUT)] ? [file normalize $::env(FB_OUT)] \
                 : $board_part ? "$area/reports/ooc/$leg/[format %.1f $period]ns" \
                 : "$area/reports/ooc/$FB_PART/$leg/[format %.1f $period]ns"}]
file mkdir $out

create_project -in_memory -part $FB_PART
set_property target_language Verilog [current_project]

switch -- $leg {
    bridge - xbar {
        lassign [filelist::flatten "$area/rtl/filelists/fb_data_fabric_$leg.f"] srcs incdirs defines
        foreach f $srcs {
            if {![file exists $f]} { puts stderr "ERROR: source not found: $f"; exit 1 }
            if {[string match *.sv $f]} { read_verilog -sv $f } else { read_verilog $f }
        }
        set_property include_dirs $incdirs [current_fileset]
    }
    sc {
        set bd [glob -nocomplain "$area/fpga/ip/build/fb_vendor_ip.srcs/sources_1/bd/fb_sc/fb_sc.bd"]
        if {$bd eq ""} { puts stderr "ERROR: fb_sc.bd missing -- run fpga/tcl/vendor_ip.tcl first"; exit 1 }
        read_bd $bd
        set_property synth_checkpoint_mode None [get_files fb_sc.bd]
        generate_target all [get_files fb_sc.bd]
        read_verilog [glob "$area/fpga/ip/build/fb_vendor_ip.gen/sources_1/bd/fb_sc/hdl/fb_sc_wrapper.v"]
        read_verilog -sv "$area/rtl/generated/fb_data_fabric_sc/fb_data_fabric.sv"
    }
    default { puts stderr "ERROR: FB_LEG must be bridge, xbar or sc, got $leg"; exit 1 }
}

set xdc "$out/ooc_clock.xdc"
set fh [open $xdc w]
puts $fh "create_clock -name aclk -period $period \[get_ports aclk\]"
close $fh
read_xdc -mode out_of_context $xdc

synth_design -top fb_data_fabric -part $FB_PART -mode out_of_context
report_utilization -file "$out/utilization_synth.txt"
opt_design
place_design
phys_opt_design
route_design

report_utilization                -file "$out/utilization.txt"
report_utilization -hierarchical  -file "$out/utilization_hier.txt"
report_timing_summary -max_paths 10 -file "$out/timing_summary.txt"
report_timing -max_paths 20 -nworst 1 -sort_by slack -file "$out/timing_worst.txt"

# summary.txt: the numbers bin/parse_ooc.py tabulates, one key per line.
# lut, ff, carry4 and muxf count primitive cells. The group names differ by
# family (7-series FLOP_LATCH / CARRY4, UltraScale+ REGISTER / CARRY8), so
# each filter names both; carry4 counts CARRY8 on UltraScale+ under the same
# key. lutram and srl are LUTs, read from report_utilization's "LUT as
# Distributed RAM" and "LUT as Shift Register" rows: a cell count cannot
# give them, since one RAM32M is four LUTs and eight primitive cells.
proc util_row {report name} {
    if {[regexp -line "^\\|\\s+$name\\s+\\|\\s+(\\d+)\\s+\\|" $report -> n]} { return $n }
    puts stderr "ERROR: no \"$name\" row in report_utilization"; exit 1
}
set util [report_utilization -return_string]
set wns  [get_property SLACK [get_timing_paths -max_paths 1 -nworst 1 -setup]]
set whs  [get_property SLACK [get_timing_paths -max_paths 1 -nworst 1 -hold]]
set path [get_timing_paths -max_paths 1 -nworst 1 -setup]
set fh [open "$out/summary.txt" w]
puts $fh "leg $leg"
puts $fh "part $FB_PART"
puts $fh "period_ns $period"
puts $fh "wns_ns $wns"
puts $fh "whs_ns $whs"
puts $fh "worst_levels [get_property LOGIC_LEVELS $path]"
puts $fh "worst_start [get_property STARTPOINT_PIN $path]"
puts $fh "worst_end [get_property ENDPOINT_PIN $path]"
puts $fh "lut [llength [get_cells -hierarchical -filter {IS_PRIMITIVE && REF_NAME =~ LUT*}]]"
puts $fh "lutram [util_row $util {LUT as Distributed RAM}]"
puts $fh "srl [util_row $util {LUT as Shift Register}]"
puts $fh "ff [llength [get_cells -hierarchical -filter {IS_PRIMITIVE && (PRIMITIVE_GROUP == FLOP_LATCH || PRIMITIVE_GROUP == REGISTER)}]]"
puts $fh "bram_tile [expr {[llength [get_cells -hierarchical -filter {IS_PRIMITIVE && REF_NAME =~ RAMB36*}]] \
                        + 0.5 * [llength [get_cells -hierarchical -filter {IS_PRIMITIVE && REF_NAME =~ RAMB18*}]]}]"
puts $fh "carry4 [llength [get_cells -hierarchical -filter {IS_PRIMITIVE && (REF_NAME == CARRY4 || REF_NAME == CARRY8)}]]"
puts $fh "muxf [llength [get_cells -hierarchical -filter {IS_PRIMITIVE && REF_NAME =~ MUXF*}]]"
close $fh
puts "\nooc_fabric: $leg @ ${period} ns -> $out (WNS $wns ns)"
