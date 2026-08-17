#==============================================================================
# create_project.tcl -- Vivado project for the STREAM MONITOR coverage build
#==============================================================================
# Board:  Digilent Genesys 2 (Kintex-7 xc7k325tffg900-2)  [genesys2-only flow]
# Top:    stream_genesys2_top  (8 channels, USE_AXI_MONITORS=1, profile tally)
# Usage:  REPO_ROOT=... STREAM_ROOT=... CONVERTERS_ROOT=... MISC_ROOT=... \
#         Run via `make project` -- fpga_flow.mk exports FPGA_FILELIST,
#         FPGA_PROJECT_ROOT, FPGA_BUILD_ROOT and the *_ROOT filelist anchors.
# The Makefile sets these env vars for you.
#==============================================================================

set project_name "stream"
set project_dir  "build/vivado_project"

# Genesys 2 only (the monitor coverage harness targets the 325T; the A7 lacks
# the BRAM/LUT headroom for 8 channels + the two profile tallies).
set part_name      "xc7k325tffg900-2"
set board_part_str "digilentinc.com:genesys2:part0:1.1"
set top_name       "stream_genesys2_top"
set top_flist_name "stream_genesys2_top.f"
set xdc_name       "stream_genesys2_top.xdc"
set board_label    "Genesys 2 (xc7k325t-2) -- monitor coverage"

set script_dir   [file dirname [file normalize [info script]]]
# The uniform flow (make/fpga_flow.mk) exports these; the fallbacks keep the
# script runnable standalone. project_root is the fpga/ dir (constraints, build,
# bitstream, reports); build_root is the build dir above it (rtl/).
set project_root [expr {[info exists ::env(FPGA_PROJECT_ROOT)] \
                        ? [file normalize $::env(FPGA_PROJECT_ROOT)] \
                        : [file normalize "$script_dir/.."]}]
set build_root   [expr {[info exists ::env(FPGA_BUILD_ROOT)] \
                        ? [file normalize $::env(FPGA_BUILD_ROOT)] \
                        : [file normalize "$script_dir/../.."]}]

foreach var {REPO_ROOT FRAMEWORK_ROOT STREAM_ROOT CONVERTERS_ROOT MISC_ROOT} {
    if {![info exists ::env($var)]} {
        puts stderr "ERROR: environment variable $var is not set. Run via the Makefile."
        exit 1
    }
}

puts "========================================================================"
puts "RTL Design Sherpa -- STREAM Monitor Coverage ($board_label)"
puts "========================================================================"
puts "Project root:     $project_root"
puts "Build root:       $build_root"
puts "Part / top:       $part_name / $top_name"
puts "========================================================================"

create_project $project_name "$project_root/$project_dir" -part $part_name -force

set obj [current_project]
set_property -name "default_lib"        -value "xil_defaultlib" -objects $obj
set_property -name "target_language"    -value "Verilog"        -objects $obj
set_property -name "simulator_language" -value "Mixed"          -objects $obj

if {[lsearch -exact [get_board_parts] $board_part_str] >= 0} {
    set_property board_part $board_part_str [current_project]
    puts "Board-part set: $board_part_str"
} else {
    puts "NOTE: board-part '$board_part_str' not available -- skipping (not required for build)."
}

# ---- Expand the top-level filelist ----
source "$script_dir/filelist_utils.tcl"
# FPGA_FILELIST is the flow's single declaration of what to build; falling back
# to the build's own rtl/filelists keeps a standalone run working.
set top_filelist [expr {[info exists ::env(FPGA_FILELIST)] \
                        ? [file normalize $::env(FPGA_FILELIST)] \
                        : "$build_root/rtl/filelists/$top_flist_name"}]
puts "\nExpanding filelist: $top_filelist"
lassign [filelist::flatten $top_filelist] sv_sources incdirs defines
puts "  [llength $sv_sources] source(s), [llength $incdirs] incdir(s), [llength $defines] define(s)"

set src_fs [get_filesets sources_1]
foreach src $sv_sources {
    if {![file exists $src]} { puts stderr "ERROR: source not found: $src"; exit 1 }
}
add_files -norecurse -fileset $src_fs $sv_sources
foreach src [get_files -of_objects $src_fs -filter {FILE_TYPE == "Verilog"}] {
    if {[string match *.sv $src] || [string match *.svh $src]} {
        set_property FILE_TYPE SystemVerilog $src
    }
}
set_property include_dirs $incdirs $src_fs
if {[llength $defines] > 0} { set_property verilog_define $defines $src_fs }

puts "Setting top module: $top_name"
set_property top $top_name $src_fs

# ---- Build-time generics (top defaults: 8ch, profile mode on, N_PROFILE=64) ----
# Override via env: STREAM_NUM_CHANNELS, MON_N_PROFILE,
# STREAM_CLKOUT0_DIVIDE (12->100 MHz; keep the XDC led_slow_clk in lockstep).
set generics {}
if {[info exists ::env(STREAM_CLKOUT0_DIVIDE)]}   { lappend generics "CLKOUT0_DIVIDE=$::env(STREAM_CLKOUT0_DIVIDE)" }
if {[info exists ::env(STREAM_NUM_CHANNELS)]}      { lappend generics "NUM_CHANNELS=$::env(STREAM_NUM_CHANNELS)" }
if {[info exists ::env(MON_N_PROFILE)]}            { lappend generics "MON_N_PROFILE=$::env(MON_N_PROFILE)" }
if {[info exists ::env(MON_ERROR_FLAVOR)]}         { lappend generics "MON_ERROR_FLAVOR=$::env(MON_ERROR_FLAVOR)" }
# Observer transaction-table sizing. OBS_MAX_TRANSACTIONS is the TOTAL slots
# per tap; the CAM is generated OBS_NUM_BANKS times at TOTAL/BANKS each,
# because timing scales with the depth of ONE cam. 64/4 = four 16-deep CAMs.
# A banked WRITE monitor also needs OBS_USE_WDATA_ORDER_Q=1 or the RTL
# refuses to elaborate.
if {[info exists ::env(OBS_MAX_TRANSACTIONS)]}     { lappend generics "OBS_MAX_TRANSACTIONS=$::env(OBS_MAX_TRANSACTIONS)" }
if {[info exists ::env(OBS_NUM_BANKS)]}            { lappend generics "OBS_NUM_BANKS=$::env(OBS_NUM_BANKS)" }
if {[info exists ::env(OBS_USE_WDATA_ORDER_Q)]}    { lappend generics "OBS_USE_WDATA_ORDER_Q=$::env(OBS_USE_WDATA_ORDER_Q)" }
if {[llength $generics] > 0} {
    puts "Applying generics: $generics"
    set_property generic $generics $src_fs
}

update_compile_order -fileset sources_1

# ---- Constraints ----
set cf [get_filesets constrs_1]
set cons_dir [expr {[info exists ::env(FPGA_CONSTRAINTS_DIR)] \
                        ? $::env(FPGA_CONSTRAINTS_DIR) \
                        : "$project_root/constraints"}]
add_files -norecurse -fileset $cf "$cons_dir/$xdc_name"

# ---- Strategies (mirror the bridge genesys2 build) ----
set_property strategy "Vivado Synthesis Defaults" [get_runs synth_1]
set impl_run [get_runs impl_1]
set_property strategy "Performance_Explore" $impl_run
set_property steps.phys_opt_design.is_enabled true $impl_run

puts "\nProject created: $project_root/$project_dir/${project_name}.xpr"
