# Filelist for ddr2_lpddr2_core_macro (SKELETON)
# Location: projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/macro/ddr2_lpddr2_core_macro.f
#
# Bundles the mid-layer macro that sits between axi_frontend_macro and
# the DFI v2.1 PHY: scheduler + per-bank/global timers + refresh +
# powerdown + init + mode register + write/read data path + DFI cmd
# formatter + DFI signal pack.

# Include directories
+incdir+$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Packages
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes/ddr2_lpddr2_pkg.sv

# FUBs
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/scheduler_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/xbank_timers_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/global_timers_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/refresh_ctrl_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/powerdown_ctrl_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/mode_register_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/init_sequencer_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/wr_beat_sequencer_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/rd_cl_aligner_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/dfi_cmd_formatter_fub.sv
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/fub/dfi_signal_pack_fub.sv

# Macro
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/macro/ddr2_lpddr2_core_macro.sv
