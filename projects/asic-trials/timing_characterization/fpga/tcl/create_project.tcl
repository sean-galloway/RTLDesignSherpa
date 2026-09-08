#==============================================================================
# create_project.tcl — Vivado project for Timing Characterization (FPGA)
#==============================================================================
# Board:  Digilent Nexys A7-100T (xc7a100tcsg324-1)
# Top:    char_top_fpga
# Usage:  REPO_ROOT=... TIMING_CHAR_ROOT=... vivado -mode batch -source create_project.tcl
# The Makefile sets these env vars for you.
#==============================================================================

set project_name "timing_char"
set project_dir  "build/vivado_project"
set part_name    "xc7a100tcsg324-1"

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]

# ----------------------------------------------------------------------------
# Env-var sanity check
# ----------------------------------------------------------------------------
foreach var {REPO_ROOT TIMING_CHAR_ROOT FPGA_FLOW_ROOT} {
    if {![info exists ::env($var)]} {
        puts stderr "ERROR: environment variable $var is not set."
        puts stderr "Run via the project Makefile (it sets them automatically),"
        puts stderr "or export them manually before invoking vivado."
        exit 1
    }
}

puts "========================================================================"
puts "RTL Design Sherpa — Timing Characterization (Nexys A7-100T)"
puts "========================================================================"
puts "Project root:      $project_root"
puts "REPO_ROOT:         $::env(REPO_ROOT)"
puts "TIMING_CHAR_ROOT:  $::env(TIMING_CHAR_ROOT)"
puts "FPGA_FLOW_ROOT:    $::env(FPGA_FLOW_ROOT)"
puts "========================================================================"

create_project $project_name "$project_root/$project_dir" -part $part_name -force

set obj [current_project]
set_property -name "default_lib"        -value "xil_defaultlib" -objects $obj
set_property -name "target_language"    -value "Verilog"         -objects $obj
set_property -name "simulator_language" -value "Mixed"           -objects $obj

# Optional board-part association — only applied if the Digilent board files
# are installed. Not required for synth/impl since the part + XDC already
# nail down the pinout.
set board_part_str "digilentinc.com:nexys-a7-100t:part0:1.3"
if {[lsearch -exact [get_board_parts] $board_part_str] >= 0} {
    set_property board_part $board_part_str [current_project]
}

# ----------------------------------------------------------------------------
# Source files
# ----------------------------------------------------------------------------
# Expand the top-level filelist into a flat list of Verilog sources, plus
# the FPGA wrapper that wraps char_top with per-FUB XOR-reduces.
source "$script_dir/filelist_utils.tcl"

set top_filelist "$::env(TIMING_CHAR_ROOT)/rtl/filelists/char_top.f"
puts "\nExpanding filelist: $top_filelist"
lassign [filelist::flatten $top_filelist] sv_sources incdirs defines

# Select the FPGA top from $FPGA_TOP (defaults to the simple wrapper).
# 'char_top_fpga'       single-clock board wrapper for normal builds.
# 'char_top_fpga_mmcm'  MMCM sweep with four test clocks + signature accumulators
#                       (see README_FPGA.md section 5).
set fpga_top "char_top_fpga"
if {[info exists ::env(FPGA_TOP)] && $::env(FPGA_TOP) ne ""} {
    set fpga_top $::env(FPGA_TOP)
}
puts "FPGA_TOP:          $fpga_top"

if {$fpga_top eq "char_top_fpga_mmcm"} {
    lappend sv_sources "$::env(FPGA_FLOW_ROOT)/rtl/sig_accum.sv"
    lappend sv_sources "$::env(FPGA_FLOW_ROOT)/rtl/char_top_fpga_mmcm.sv"
} else {
    lappend sv_sources "$::env(FPGA_FLOW_ROOT)/rtl/char_top_fpga.sv"
}

set src_fs [get_filesets sources_1]

puts "\nAdding [llength $sv_sources] Verilog sources..."
foreach src $sv_sources {
    if {![file exists $src]} {
        puts stderr "ERROR: source file missing: $src"
        exit 1
    }
}

add_files -norecurse -fileset $src_fs $sv_sources

# Mark .sv / .svh files as SystemVerilog so Vivado parses them with sv2012.
foreach src $sv_sources {
    if {[string match *.sv $src] || [string match *.svh $src]} {
        set_property file_type "SystemVerilog" [get_files -of $src_fs $src]
    }
}

set_property -name "include_dirs" -value $incdirs -objects $src_fs

if {[llength $defines] > 0} {
    puts "Verilog defines: $defines"
    set_property -name "verilog_define" -value $defines -objects $src_fs
}

# Top module follows whichever wrapper we added above.
set top_name $fpga_top
set_property top $top_name $src_fs
puts "\nTop module: $top_name"

# ----------------------------------------------------------------------------
# Constraints - one XDC per FPGA top variant.
# ----------------------------------------------------------------------------
set cf [get_filesets constrs_1]
if {$fpga_top eq "char_top_fpga_mmcm"} {
    set xdc_path "$::env(FPGA_FLOW_ROOT)/constraints/char_top_fpga_mmcm.xdc"
} else {
    set xdc_path "$::env(FPGA_FLOW_ROOT)/constraints/char_top_fpga.xdc"
}
add_files -norecurse -fileset $cf $xdc_path
set_property file_type XDC [get_files -of $cf $xdc_path]

# Dynamic create_clock from TARGET_PERIOD_NS (default 10.0 = 100 MHz).
# Used by `make bitstream-sweep` to tighten the period across runs.
source "$script_dir/clock_constraint.tcl"

puts "\nProject created at $project_root/$project_dir"
puts "========================================================================"
