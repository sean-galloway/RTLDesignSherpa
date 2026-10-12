# ==============================================================================
# pumice (DDR2/LPDDR2 memory controller) - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns, so that
#          `make lint-mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2` has sources.
# Usage:   verilator --lint-only -f filelists/pumice_all.f
#
# `-f` includes each block s own filelist; never hand-list sources here.
#
# rtl/OLD/ is deliberately NOT referenced: pumice_bank_sched_core and
# pumice_bank_cmd_picker are the retired two-stage bank scheduler, set aside
# for timing. They are in no filelist on purpose, so lint does not gate them.
# ==============================================================================

+incdir+$REPO_ROOT/rtl/amba/includes

# --- CSR ---
-f $REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/filelists/pumice_csr.f

# --- FUBs ---
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_global_timers.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_xddr2_init_sequencer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_xddr2_mode_register.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_timers.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_cmd_history_checker.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_page_policy.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_storage_plane.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_xddr2_refresh_ctrl.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_lpddr2_zq_ctrl.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_lpddr2_dq_cal.f

# --- Macros ---
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_axi4_plane.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_dfi_2p1_plane.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_scheduler_plane.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_training_plane.f

# --- Tops ---
-f $REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/filelists/top/pumice_core.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/filelists/top/pumice_top.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/filelists/top/pumice_top_geared.f
