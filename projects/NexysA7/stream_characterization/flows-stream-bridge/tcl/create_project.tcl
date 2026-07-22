#==============================================================================
# create_project.tcl — Vivado project for STREAM Characterization
#==============================================================================
# Board:  Digilent Nexys A7-100T (xc7a100tcsg324-1)
# Top:    stream_char_top
# Usage:  REPO_ROOT=... STREAM_ROOT=... CONVERTERS_ROOT=... MISC_ROOT=... \
#         STREAM_CHAR_ROOT=... vivado -mode batch -source create_project.tcl
# The Makefile sets these env vars for you.
#==============================================================================

set project_name "stream_char"
set project_dir  "build/vivado_project"

# Board target selection (env BOARD=nexys|genesys2; default nexys). The
# genesys2 target is the Kintex-7 325T-2 monitor board-validation build
# (stream_char_genesys2_top: MMCM 200 MHz LVDS -> harness clock, 4 channels,
# USE_AXI_MONITORS=1). Mirrors the rapids_char BOARD switch.
set part_name      "xc7a100tcsg324-1"
set board_part_str "digilentinc.com:nexys-a7-100t:part0:1.3"
set top_name       "stream_char_top"
set top_flist_name "stream_char_top.f"
set xdc_name       "stream_char_top.xdc"
set board_label    "Nexys A7-100T (xc7a100t-1)"
if {[info exists ::env(BOARD)] && $::env(BOARD) eq "genesys2"} {
    set part_name      "xc7k325tffg900-2"
    set board_part_str "digilentinc.com:genesys2:part0:1.1"
    set top_name       "stream_char_genesys2_top"
    set top_flist_name "stream_char_genesys2_top.f"
    set xdc_name       "stream_char_genesys2_top.xdc"
    set board_label    "Genesys 2 (xc7k325t-2)"
}

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]

# ----------------------------------------------------------------------------
# Env-var sanity check
# ----------------------------------------------------------------------------
foreach var {REPO_ROOT FRAMEWORK_ROOT STREAM_ROOT CONVERTERS_ROOT MISC_ROOT STREAM_CHAR_ROOT} {
    if {![info exists ::env($var)]} {
        puts stderr "ERROR: environment variable $var is not set."
        puts stderr "Run via the project Makefile (it sets them automatically),"
        puts stderr "or export them manually before invoking vivado."
        exit 1
    }
}

puts "========================================================================"
puts "RTL Design Sherpa — STREAM Characterization ($board_label)"
puts "========================================================================"
puts "Project root:     $project_root"
puts "REPO_ROOT:        $::env(REPO_ROOT)"
puts "STREAM_CHAR_ROOT: $::env(STREAM_CHAR_ROOT)"
puts "Part / top:       $part_name / $top_name"
puts "========================================================================"

create_project $project_name "$project_root/$project_dir" -part $part_name -force

set obj [current_project]
set_property -name "default_lib"        -value "xil_defaultlib" -objects $obj
set_property -name "target_language"    -value "Verilog"         -objects $obj
set_property -name "simulator_language" -value "Mixed"           -objects $obj

# Optional board-part association — only applied if the Digilent board files
# are installed. Not required for synthesis/impl since the part is already set
# and the XDC handles all pin mapping.
if {[lsearch -exact [get_board_parts] $board_part_str] >= 0} {
    set_property board_part $board_part_str [current_project]
    puts "Board-part set: $board_part_str"
} else {
    puts "NOTE: board-part '$board_part_str' not available — skipping."
    puts "      (Install Digilent board files to enable; not required for build.)"
}

# ----------------------------------------------------------------------------
# Expand the top-level filelist into a flat list of Verilog sources.
# ----------------------------------------------------------------------------
source "$script_dir/filelist_utils.tcl"

set top_filelist "$::env(STREAM_CHAR_ROOT)/rtl/filelists/$top_flist_name"
puts "\nExpanding filelist: $top_filelist"
lassign [filelist::flatten $top_filelist] sv_sources incdirs defines

puts "  [llength $sv_sources] source file(s)"
puts "  [llength $incdirs] include directory(ies)"
puts "  [llength $defines] macro define(s)"

# ----------------------------------------------------------------------------
# Add sources / set top
# ----------------------------------------------------------------------------
set src_fs [get_filesets sources_1]
foreach src $sv_sources {
    if {![file exists $src]} {
        puts stderr "ERROR: source not found: $src"
        exit 1
    }
}
# Single add_files call — much faster than one-at-a-time for 70+ files.
add_files -norecurse -fileset $src_fs $sv_sources

# Flag SystemVerilog where needed (Vivado relies on file extension, but be
# explicit for any file with ambiguous extensions).
foreach src [get_files -of_objects $src_fs -filter {FILE_TYPE == "Verilog"}] {
    if {[string match *.sv $src] || [string match *.svh $src]} {
        set_property FILE_TYPE SystemVerilog $src
    }
}

# Include directories
set_property include_dirs $incdirs $src_fs

# Verilog defines (if the filelist provides any)
if {[llength $defines] > 0} {
    set_property verilog_define $defines $src_fs
}

puts "Setting top module: $top_name"
set_property top $top_name $src_fs

# Genesys 2 build-time knobs (top-level generics). STREAM_CLKOUT0_DIVIDE sets
# the MMCM CLKOUT0 divider (12 -> 100 MHz, 15 -> 80 MHz, 20 -> 60 MHz); keep
# the XDC led_slow_clk -divide_by in lockstep when changing it.
# STREAM_NUM_CHANNELS overrides the channel count (default 4 in the wrapper;
# HARD boundary <= 4 until the 8-channel engine wedge is root-caused).
if {[info exists ::env(BOARD)] && $::env(BOARD) eq "genesys2"} {
    set generics {}
    if {[info exists ::env(STREAM_CLKOUT0_DIVIDE)]} {
        lappend generics "CLKOUT0_DIVIDE=$::env(STREAM_CLKOUT0_DIVIDE)"
    }
    if {[info exists ::env(STREAM_NUM_CHANNELS)]} {
        lappend generics "NUM_CHANNELS=$::env(STREAM_NUM_CHANNELS)"
    }
    if {[llength $generics] > 0} {
        puts "Applying generics: $generics"
        set_property generic $generics $src_fs
    }
}

update_compile_order -fileset sources_1

# ----------------------------------------------------------------------------
# Constraints
# ----------------------------------------------------------------------------
set cf [get_filesets constrs_1]
add_files -norecurse -fileset $cf \
    "$project_root/constraints/$xdc_name"

# ----------------------------------------------------------------------------
# Synthesis / implementation strategy
#
# Synthesis: defaults (8-channel stream_char synthesizes cleanly without
# strategy tuning).
#
# Implementation: Performance_Explore. Defaults left WNS at -17 ps on a single
# endpoint in the descriptor AXI monitor's trans_mgr active-count carry chain
# (a 13-level / 7.3 ns-routed cone). The path is observability-side and the
# slack is well within seed noise, so an Explore strategy that tries a few
# place/route variations closes it without RTL changes. If we ever need more
# headroom, Performance_ExplorePostRoutePhysOpt adds an extra phys-opt pass.
# ----------------------------------------------------------------------------
set synth_run [get_runs synth_1]
set_property strategy "Vivado Synthesis Defaults" $synth_run

set impl_run [get_runs impl_1]
set_property strategy "Performance_Explore" $impl_run
set_property steps.phys_opt_design.is_enabled true $impl_run

puts "\nProject created: $project_root/$project_dir/${project_name}.xpr"
puts "Next:  source $script_dir/build_all.tcl"
