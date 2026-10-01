# ==============================================================================
# scoria (DDR3/LPDDR3 memory controller) - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns, so that
#          `make lint-mem-ctrl-ip/scoria-ddr3-lpddr3` has sources.
# Usage:   verilator --lint-only -f filelists/scoria_all.f
#
# `-f` includes each block's own filelist; never hand-list sources here.
#
# Written 2026-09-30. Until then this area had no rtl/Makefile and no master
# filelist, so it had NO lint gate at all -- and registering it in
# projects/components/Makefile's COMPONENTS list would have broken the repo's
# `make lint-all`, which runs `make -C <comp>/rtl lint-all` for every entry and
# exits on the first failure.
#
# It names every FUB, including the two nothing instantiates
# (scoria_powerdown_ctrl, scoria_dfi_signal_pack -- see
# scoria-ddr3-lpddr3 TASK-003). A module outside the lint closure is a module
# whose next edit is checked by nothing.
# ==============================================================================

+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/includes

# --- FUBs ---
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_addr_mapper.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_axi_burst_chopper.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_bank_timers.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_cmd_arbiter.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_cmd_history_checker.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_dfi_cdc.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_dfi_cmd_formatter.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_dfi_cmd_path.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_dfi_rd_aligner.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_dfi_signal_pack.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_dfi_wr_serializer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_global_timers.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_init_sequencer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_mode_register.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_page_policy.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_powerdown_ctrl.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_rd_cmd_cam.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_rd_intake.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_rd_return_ring.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_refresh_ctrl.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_wr_data_cam.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_wr_intake.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_wrlvl_ifc.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_wr_splitter.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_zq_ctrl.f

# --- macro tier ---
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/macro/scoria_axi4_ifc.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/macro/scoria_dfi_layer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/macro/scoria_mem_cmd_scheduler.f

# --- top tier (pulls the generated CSR block) ---
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/top/scoria_core.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/top/scoria_top.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/filelists/top/scoria_top_geared.f
