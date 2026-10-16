#==============================================================================
# create_project.tcl -- fabric benchmark board build (Genesys 2), one leg
#==============================================================================
# Run through the area's build-<leg>/Makefile (make/fpga_flow.mk), which sets:
#   FPGA_FILELIST        rtl/filelists/fb_genesys2_top_<leg>.f -- the leg is
#                        whichever fb_data_fabric that filelist compiles
#   FPGA_PROJECT_ROOT    build-<leg>/fpga: where Vivado writes
#   FPGA_CONSTRAINTS_DIR fpga/constraints (shared by every leg)
#   FB_LEG               sc for leg B2 (creates the SmartConnect block design)
# and the filelist anchors (REPO_ROOT, STREAM_ROOT, STREAM_CHAR_FRAMEWORK_ROOT,
# CONVERTERS_ROOT, MISC_ROOT; XILINX_VIVADO for leg B1's crossbar HDL).
# The S0 controller (fb_mig) is created IN this project from the same .prj as
# the vendor-IP project (fb_mig_ip.tcl), so builds never share an IP dir.
#==============================================================================
set script_dir [file dirname [file normalize [info script]]]
set area       [file normalize "$script_dir/../.."]
foreach var {REPO_ROOT FPGA_FILELIST FPGA_PROJECT_ROOT STREAM_ROOT STREAM_CHAR_FRAMEWORK_ROOT CONVERTERS_ROOT MISC_ROOT} {
    if {![info exists ::env($var)]} {
        puts stderr "ERROR: environment variable $var is not set. Run via build-<leg>/Makefile."
        exit 1
    }
}
source "$area/rtl/generated/fb_vendor_ip_cfg/fb_vendor_ip_cfg.tcl"
source "$::env(REPO_ROOT)/make/tcl/filelist_utils.tcl"
source "$script_dir/fb_mig_ip.tcl"

set project_root [file normalize $::env(FPGA_PROJECT_ROOT)]
set project_name [expr {[info exists ::env(FLOW)] ? $::env(FLOW) : "fb"}]
set top_name     fb_genesys2_top
set cons_dir     [expr {[info exists ::env(FPGA_CONSTRAINTS_DIR)] \
                        ? $::env(FPGA_CONSTRAINTS_DIR) : "$area/fpga/constraints"}]

puts "========================================================================"
puts "Fabric benchmark -- Genesys 2 board build ($project_name)"
puts "  part     $FB_PART"
puts "  filelist $::env(FPGA_FILELIST)"
puts "========================================================================"

create_project $project_name "$project_root/build/vivado_project" -part $FB_PART -force
set_property target_language Verilog [current_project]

lassign [filelist::flatten $::env(FPGA_FILELIST)] sv_sources incdirs defines
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

fb_create_mig $area $FB_DW $FB_SID

# Leg B2: SmartConnect is a block design, created in this project from the same
# configuration as the vendor-IP project (fb_sc_bd.tcl); its wrapper
# (fb_sc_wrapper) is what rtl/generated/fb_data_fabric_sc/fb_data_fabric.sv wraps.
if {[info exists ::env(FB_LEG)] && $::env(FB_LEG) eq "sc"} {
    source "$script_dir/fb_sc_bd.tcl"
    fb_create_sc_bd
    # Synthesize the block design out of context, in its own compilation unit.
    # Global mode (None, as fb_create_sc_bd leaves it for the OOC fabric
    # measurement) compiles SmartConnect's encrypted sources beside ours, and
    # its $unit declarations collide with rtl/amba/includes/fifo_defs.svh
    # ("'FIFO_BRAM' is already declared", Synth 8-8891).
    set bd_file [get_files fb_sc.bd]
    set_property synth_checkpoint_mode Singular $bd_file
    generate_target all $bd_file
}

set_property top $top_name $src_fs
update_compile_order -fileset sources_1

add_files -norecurse -fileset [get_filesets constrs_1] "$cons_dir/fb_genesys2_top.xdc"

set impl_run [get_runs impl_1]
set_property strategy "Performance_Explore" $impl_run
set_property steps.phys_opt_design.is_enabled true $impl_run
puts "\nProject created: $project_root/build/vivado_project/${project_name}.xpr"
