#==============================================================================
# Vivado Project Creation Script
#==============================================================================
# Project: CDC Counter Display
# Board: Nexys A7-100T
# Purpose: Create Vivado project and add all sources
#==============================================================================

## Set project parameters
set project_name "cdc_counter_display"
set project_dir "vivado_project"
set part_name "xc7a100tcsg324-1"

## Get script directory (works regardless of where script is called from)
set script_dir [file dirname [file normalize [info script]]]
set repo_root [file normalize "$script_dir/../../.."]
set project_root "$script_dir/.."

puts "========================================================================"
puts "RTL Design Sherpa - CDC Counter Display Project"
puts "========================================================================"
puts "Repository root: $repo_root"
puts "Project root: $project_root"
puts "Creating Vivado project: $project_name"
puts "========================================================================"

## Create project
create_project $project_name "$project_root/$project_dir" -part $part_name -force

## Set project properties
set obj [current_project]
set_property -name "default_lib" -value "xil_defaultlib" -objects $obj
set_property -name "enable_vhdl_2008" -value "1" -objects $obj
set_property -name "ip_cache_permissions" -value "read write" -objects $obj
set_property -name "ip_output_repo" -value "$project_root/$project_dir/${project_name}.cache/ip" -objects $obj
set_property -name "mem.enable_memory_map_generation" -value "1" -objects $obj
set_property -name "sim.central_dir" -value "$project_root/$project_dir/${project_name}.ip_user_files" -objects $obj
set_property -name "sim.ip.auto_export_scripts" -value "1" -objects $obj
set_property -name "simulator_language" -value "Mixed" -objects $obj
set_property -name "target_language" -value "Verilog" -objects $obj

## Set board part (Nexys A7-100T)
set_property board_part digilentinc.com:nexys-a7-100t:part0:1.3 [current_project]

puts "\nAdding source files..."

#==============================================================================
# Add RTL Design Sources
#==============================================================================

## Create fileset
set src_fileset [get_filesets sources_1]

## Add top-level design
add_files -norecurse -fileset $src_fileset "$project_root/rtl/cdc_counter_display_top.sv"

## Add rtldesignsherpa common library modules
puts "  Adding rtldesignsherpa common library modules..."

## Clock utilities
add_files -norecurse -fileset $src_fileset "$repo_root/rtl/common/clock_divider.sv"

## Debounce
add_files -norecurse -fileset $src_fileset "$repo_root/rtl/common/debounce.sv"

## Synchronizers
add_files -norecurse -fileset $src_fileset "$repo_root/rtl/common/sync_pulse.sv"

## Note: sync_pulse may depend on sync_2ff - check and add if needed
if {[file exists "$repo_root/rtl/common/sync_2ff.sv"]} {
    add_files -norecurse -fileset $src_fileset "$repo_root/rtl/common/sync_2ff.sv"
    puts "    Added sync_2ff.sv (dependency of sync_pulse)"
}

## Display utilities
add_files -norecurse -fileset $src_fileset "$repo_root/rtl/common/hex_to_7seg.sv"

## Set top module
set_property top cdc_counter_display_top [current_fileset]
update_compile_order -fileset sources_1

puts "  Source files added successfully"

#==============================================================================
# Add Constraints
#==============================================================================

puts "\nAdding constraints..."

## Create constraints fileset
set const_fileset [get_filesets constrs_1]

## Add XDC constraints
add_files -norecurse -fileset $const_fileset "$project_root/constraints/nexys_a7_100t.xdc"

puts "  Constraints added successfully"

#==============================================================================
# Set Synthesis Strategy
#==============================================================================

puts "\nConfiguring synthesis..."

set synth_run [get_runs synth_1]
set_property strategy "Vivado Synthesis Defaults" $synth_run
set_property steps.synth_design.args.flatten_hierarchy "rebuilt" $synth_run
set_property steps.synth_design.args.directive "Default" $synth_run
set_property steps.synth_design.args.fsm_extraction "auto" $synth_run
set_property steps.synth_design.args.keep_equivalent_registers "false" $synth_run
set_property steps.synth_design.args.resource_sharing "auto" $synth_run
set_property steps.synth_design.args.no_lc "false" $synth_run
set_property steps.synth_design.args.shreg_min_size "3" $synth_run

puts "  Synthesis configured"

#==============================================================================
# Set Implementation Strategy
#==============================================================================

puts "\nConfiguring implementation..."

set impl_run [get_runs impl_1]
set_property strategy "Vivado Implementation Defaults" $impl_run
set_property steps.opt_design.args.directive "Default" $impl_run
set_property steps.place_design.args.directive "Default" $impl_run
set_property steps.phys_opt_design.is_enabled "true" $impl_run
set_property steps.phys_opt_design.args.directive "Default" $impl_run
set_property steps.route_design.args.directive "Default" $impl_run
set_property steps.post_route_phys_opt_design.is_enabled "true" $impl_run
set_property steps.post_route_phys_opt_design.args.directive "Default" $impl_run

puts "  Implementation configured"

#==============================================================================
# Create Simulation Fileset (Optional)
#==============================================================================

## Note: CocoTB testbench is separate - this is for basic Vivado simulation

puts "\nProject created successfully!"
puts "========================================================================"
puts "Next steps:"
puts "  1. Review project in Vivado GUI: vivado $project_root/$project_dir/${project_name}.xpr"
puts "  2. Run synthesis: source $script_dir/run_synthesis.tcl"
puts "  3. Run implementation: source $script_dir/run_implementation.tcl"
puts "  4. Generate bitstream: source $script_dir/generate_bitstream.tcl"
puts "  5. Or run full build: source $script_dir/build_all.tcl"
puts "========================================================================"
