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

# Append the FPGA wrapper (not part of the ASIC filelist).
lappend sv_sources "$::env(FPGA_FLOW_ROOT)/rtl/char_top_fpga.sv"

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

# Top module
set top_name "char_top_fpga"
set_property top $top_name $src_fs
puts "\nTop module: $top_name"

# ----------------------------------------------------------------------------
# Constraints
# ----------------------------------------------------------------------------
set cf [get_filesets constrs_1]
add_files -norecurse -fileset $cf \
    "$::env(FPGA_FLOW_ROOT)/constraints/char_top_fpga.xdc"
set_property file_type XDC \
    [get_files -of $cf "$::env(FPGA_FLOW_ROOT)/constraints/char_top_fpga.xdc"]

puts "\nProject created at $project_root/$project_dir"
puts "========================================================================"
