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
set project_dir  "vivado_project"
set part_name    "xc7a100tcsg324-1"

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]

# ----------------------------------------------------------------------------
# Env-var sanity check
# ----------------------------------------------------------------------------
foreach var {REPO_ROOT STREAM_ROOT CONVERTERS_ROOT MISC_ROOT STREAM_CHAR_ROOT} {
    if {![info exists ::env($var)]} {
        puts stderr "ERROR: environment variable $var is not set."
        puts stderr "Run via the project Makefile (it sets them automatically),"
        puts stderr "or export them manually before invoking vivado."
        exit 1
    }
}

puts "========================================================================"
puts "RTL Design Sherpa — STREAM Characterization (Nexys A7-100T)"
puts "========================================================================"
puts "Project root:     $project_root"
puts "REPO_ROOT:        $::env(REPO_ROOT)"
puts "STREAM_CHAR_ROOT: $::env(STREAM_CHAR_ROOT)"
puts "========================================================================"

create_project $project_name "$project_root/$project_dir" -part $part_name -force

set obj [current_project]
set_property -name "default_lib"        -value "xil_defaultlib" -objects $obj
set_property -name "target_language"    -value "Verilog"         -objects $obj
set_property -name "simulator_language" -value "Mixed"           -objects $obj

# Optional board-part association — only applied if the Digilent board files
# are installed. Not required for synthesis/impl since the part is already set
# and the XDC handles all pin mapping.
set board_part_str "digilentinc.com:nexys-a7-100t:part0:1.3"
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

set top_filelist "$::env(STREAM_CHAR_ROOT)/rtl/filelists/stream_char_top.f"
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

set_property top stream_char_top $src_fs
update_compile_order -fileset sources_1

# ----------------------------------------------------------------------------
# Constraints
# ----------------------------------------------------------------------------
set cf [get_filesets constrs_1]
add_files -norecurse -fileset $cf \
    "$project_root/constraints/stream_char_top.xdc"

# ----------------------------------------------------------------------------
# Synthesis / implementation strategy — defaults are fine for first bring-up.
# ----------------------------------------------------------------------------
set synth_run [get_runs synth_1]
set_property strategy "Vivado Synthesis Defaults" $synth_run

set impl_run [get_runs impl_1]
set_property strategy "Vivado Implementation Defaults" $impl_run
set_property steps.phys_opt_design.is_enabled true $impl_run

puts "\nProject created: $project_root/$project_dir/${project_name}.xpr"
puts "Next:  source $script_dir/build_all.tcl"
