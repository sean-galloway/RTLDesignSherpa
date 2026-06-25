#==============================================================================
# Vivado Project Creation Script — CDC Counter Display (Phase 2 / UART harness)
#==============================================================================
# Project: cdc_demo
# Board:   Nexys A7-100T  (xc7a100tcsg324-1)
# Top:    cdc_demo_top
# Purpose: Build the harness-driven CDC demo with UART + 4 buttons + 7-seg.
#
# This is the phase-2 sibling to create_project.tcl (which builds the
# button-only cdc_counter_display_top). Both projects live in
# vivado_project*/ subdirectories so they can coexist.
#==============================================================================

set project_name "cdc_demo"
set project_dir  "vivado_project_demo"
set part_name    "xc7a100tcsg324-1"

set script_dir   [file dirname [file normalize [info script]]]
set repo_root    [file normalize "$script_dir/../../../.."]
set project_root [file normalize "$script_dir/.."]

puts "========================================================================"
puts "RTL Design Sherpa — CDC Demo (UART harness, Phase 2)"
puts "========================================================================"
puts "Repository root: $repo_root"
puts "Project root:    $project_root"
puts "Creating Vivado project: $project_name"
puts "========================================================================"

create_project $project_name "$project_root/$project_dir" -part $part_name -force

set obj [current_project]
set_property -name "default_lib"        -value "xil_defaultlib" -objects $obj
set_property -name "target_language"    -value "Verilog"         -objects $obj
set_property -name "simulator_language" -value "Mixed"           -objects $obj

set board_part_str "digilentinc.com:nexys-a7-100t:part0:1.3"
if {[lsearch -exact [get_board_parts] $board_part_str] >= 0} {
    set_property board_part $board_part_str [current_project]
}

#------------------------------------------------------------------------------
# Source files
#------------------------------------------------------------------------------
set src_fs [get_filesets sources_1]

# Project RTL (phase-2)
add_files -norecurse -fileset $src_fs [list \
    "$project_root/rtl/cdc_demo_top.sv" \
    "$project_root/rtl/cdc_demo_harness.sv" \
    "$project_root/rtl/cdc_counter_domain.sv" \
]

# Common library deps
add_files -norecurse -fileset $src_fs [list \
    "$repo_root/rtl/common/clock_divider.sv" \
    "$repo_root/rtl/common/gray2bin.sv" \
    "$repo_root/rtl/common/bin2gray.sv" \
    "$repo_root/rtl/common/sync_pulse.sv" \
    "$repo_root/rtl/common/fifo_sync.sv" \
    "$repo_root/rtl/common/fifo_async.sv" \
    "$repo_root/rtl/common/fifo_control.sv" \
    "$repo_root/rtl/common/counter_bin.sv" \
    "$repo_root/rtl/common/counter_bin_load.sv" \
    "$repo_root/rtl/common/counter_bingray.sv" \
    "$repo_root/rtl/common/glitch_free_n_dff_arn.sv" \
    "$repo_root/rtl/amba/shared/cdc_synchronizer.sv" \
    "$repo_root/rtl/amba/shared/cdc_open_loop.sv" \
    "$repo_root/rtl/amba/shared/cdc_2_phase_handshake.sv" \
    "$repo_root/rtl/amba/shared/cdc_4_phase_handshake.sv" \
]

# UART AXIL bridge + AXIL master halves it depends on
add_files -norecurse -fileset $src_fs [list \
    "$repo_root/projects/components/converters/rtl/uart_to_axil4/uart_rx.sv" \
    "$repo_root/projects/components/converters/rtl/uart_to_axil4/uart_tx.sv" \
    "$repo_root/projects/components/converters/rtl/uart_to_axil4/uart_axil_bridge.sv" \
    "$repo_root/rtl/amba/axil4/axil4_master_rd.sv" \
    "$repo_root/rtl/amba/axil4/axil4_master_wr.sv" \
    "$repo_root/rtl/amba/gaxi/gaxi_fifo_sync.sv" \
    "$repo_root/rtl/amba/gaxi/gaxi_skid_buffer.sv" \
]

# Mark all .sv files as SystemVerilog
foreach f [get_files -of $src_fs *.sv] {
    set_property file_type "SystemVerilog" $f
}

# Include dir for reset_defs.svh
set_property -name "include_dirs" \
    -value [list "$repo_root/rtl/amba/includes"] -objects $src_fs

set_property top cdc_demo_top $src_fs

#------------------------------------------------------------------------------
# Constraints
#------------------------------------------------------------------------------
set cf [get_filesets constrs_1]
add_files -norecurse -fileset $cf "$project_root/constraints/cdc_demo.xdc"
set_property file_type XDC [get_files -of $cf "$project_root/constraints/cdc_demo.xdc"]

#------------------------------------------------------------------------------
# Strategies
#------------------------------------------------------------------------------
set_property strategy "Vivado Synthesis Defaults" [get_runs synth_1]
set_property strategy "Vivado Implementation Defaults" [get_runs impl_1]

puts ""
puts "Project created at $project_root/$project_dir"
puts "Top: cdc_demo_top"
puts "========================================================================"
