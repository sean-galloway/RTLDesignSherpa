#==============================================================================
# create_project.tcl — Vivado project for the MCDMA characterization flow
#==============================================================================
# Board:  Digilent Nexys A7-100T (xc7a100tcsg324-1)
# Top:    vivado_mcdma_top
# Usage:  Run via the project Makefile (sets the env vars below).
#==============================================================================

set project_name "vivado_mcdma"
set project_dir  "build/vivado_project"
set part_name    "xc7a100tcsg324-1"

set script_dir   [file dirname [file normalize [info script]]]
set project_root [file normalize "$script_dir/.."]

# ----------------------------------------------------------------------------
# Env-var sanity check
# ----------------------------------------------------------------------------
foreach var {REPO_ROOT FRAMEWORK_ROOT RTL_VIVADO_ROOT MCDMA_FLOW_ROOT
             STREAM_ROOT CONVERTERS_ROOT MISC_ROOT} {
    if {![info exists ::env($var)]} {
        puts stderr "ERROR: environment variable $var is not set."
        puts stderr "Run via the project Makefile (it sets them automatically),"
        puts stderr "or export them manually before invoking vivado."
        exit 1
    }
}

puts "========================================================================"
puts "RTL Design Sherpa — Vivado MCDMA Characterization (Nexys A7-100T)"
puts "========================================================================"
puts "Project root:    $project_root"
puts "REPO_ROOT:       $::env(REPO_ROOT)"
puts "FRAMEWORK_ROOT:  $::env(FRAMEWORK_ROOT)"
puts "RTL_VIVADO_ROOT: $::env(RTL_VIVADO_ROOT)"
puts "MCDMA_FLOW_ROOT: $::env(MCDMA_FLOW_ROOT)"
puts "========================================================================"

create_project $project_name "$project_root/$project_dir" -part $part_name -force

set obj [current_project]
set_property -name "default_lib"        -value "xil_defaultlib" -objects $obj
set_property -name "target_language"    -value "Verilog"        -objects $obj
set_property -name "simulator_language" -value "Mixed"          -objects $obj

# Optional board-part association (no-op if Digilent files aren't installed).
set board_part_str "digilentinc.com:nexys-a7-100t:part0:1.3"
if {[lsearch -exact [get_board_parts] $board_part_str] >= 0} {
    set_property board_part $board_part_str [current_project]
    puts "Board-part set: $board_part_str"
} else {
    puts "NOTE: board-part '$board_part_str' not available — skipping."
}

# ----------------------------------------------------------------------------
# Add the Vivado MCDMA IP (.xci) to the project. Vivado will auto-generate
# the synthesis / sim products on the next build.
# ----------------------------------------------------------------------------
set mcdma_xci "$::env(RTL_VIVADO_ROOT)/axi_mcdma_0/axi_mcdma_0.xci"
if {![file exists $mcdma_xci]} {
    puts stderr "ERROR: MCDMA IP not found: $mcdma_xci"
    exit 1
}
puts "\nAdding MCDMA IP: $mcdma_xci"
import_ip $mcdma_xci
upgrade_ip [get_ips axi_mcdma_0]

# ----------------------------------------------------------------------------
# Expand the top-level filelist into a flat list of Verilog sources.
# ----------------------------------------------------------------------------
# The flow shares the existing filelist util with flows-stream-bridge — copy
# it locally so the two flows are independent.
source "$script_dir/filelist_utils.tcl"

set top_filelist "$::env(MCDMA_FLOW_ROOT)/rtl/filelists/vivado_mcdma_top.f"
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
add_files -norecurse -fileset $src_fs $sv_sources

foreach src [get_files -of_objects $src_fs -filter {FILE_TYPE == "Verilog"}] {
    if {[string match *.sv $src] || [string match *.svh $src]} {
        set_property FILE_TYPE SystemVerilog $src
    }
}

set_property include_dirs $incdirs $src_fs
if {[llength $defines] > 0} {
    set_property verilog_define $defines $src_fs
}

set top_name vivado_mcdma_top
puts "Setting top module: $top_name"
set_property top $top_name $src_fs
update_compile_order -fileset sources_1

# ----------------------------------------------------------------------------
# Constraints
# ----------------------------------------------------------------------------
set cf [get_filesets constrs_1]
add_files -norecurse -fileset $cf \
    "$project_root/constraints/vivado_mcdma_top.xdc"

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
