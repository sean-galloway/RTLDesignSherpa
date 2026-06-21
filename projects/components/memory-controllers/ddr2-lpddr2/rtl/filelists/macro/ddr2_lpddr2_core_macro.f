# Filelist for ddr2_lpddr2_core_macro (SKELETON)
# Location: projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/macro/ddr2_lpddr2_core_macro.f
#
# Slim top wrapper: instantiates the three sub-macros that together
# form the controller core (scheduler + data path + DFI v2.1 wire pack).

+incdir+$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes/ddr2_lpddr2_pkg.sv

# FUBs — listed once at the top so each sub-macro elaborates clean
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/scheduler.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/xbank_timers.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/global_timers.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/refresh_ctrl.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/powerdown_ctrl.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/mode_register.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/init_sequencer.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/wr_beat_sequencer.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/rd_cl_aligner.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/dfi_cmd_formatter.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/dfi_signal_pack.sv

# Sub-macros (each wraps a coherent FUB group)
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/macro/command_scheduler_macro.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/macro/data_path_macro.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/macro/dfi_v21_interface_macro.sv

# Top wrapper
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/macro/ddr2_lpddr2_core_macro.sv
