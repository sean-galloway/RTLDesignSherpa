# Filelist for ddr2_lpddr2_core_macro
# Location: projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/macro/ddr2_lpddr2_core_macro.f
#
# AXI-to-DFI macro: AXI4 host frontend + scheduler + data path + DFI v2.1
# wire pack. As of 2026-06-26 the macro absorbs axi_frontend_macro, so its
# port boundary is AXI4 slave on the host side and DFI v2.1 on the memory
# side. CSR slave is at the next layer up (ddr2_lpddr2_top).

+incdir+$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes/ddr2_lpddr2_pkg.sv

# Common cells used by both frontend and scheduler/datapath
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_wr.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv

# Frontend FUBs
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/addr_mapper.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/wr_cmd_cam.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/rd_cmd_cam.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/wr2rd_forward.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/axi_id_side_table.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/axi_intake.sv

# Frontend macro
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/macro/axi_frontend_macro.sv

# Scheduler + data-path + DFI FUBs
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/scheduler.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/xbank_timers.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/global_timers.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/refresh_ctrl.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/powerdown_ctrl.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/mode_register.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/init_sequencer.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/page_predictor.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/wr_beat_sequencer.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/rd_cl_aligner.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/dfi_cmd_formatter.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/dfi_signal_pack.sv

# Sub-macros (each wraps a coherent FUB group)
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/macro/command_scheduler_macro.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/macro/data_path_macro.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/macro/dfi_v21_interface_macro.sv

# Core macro (contains all of the above)
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/macro/ddr2_lpddr2_core_macro.sv
