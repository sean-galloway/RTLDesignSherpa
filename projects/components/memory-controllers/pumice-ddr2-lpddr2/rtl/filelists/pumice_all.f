# ==============================================================================
# pumice (DDR2/LPDDR2 memory controller) - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns, so that
#          `make lint-memory-controllers/pumice-ddr2-lpddr2` has sources.
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
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/pumice_csr.f

# --- FUBs ---
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/addr_mapper.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/dfi_cmd_formatter.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/dfi_signal_pack.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/global_timers.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/init_sequencer.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/mode_register.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/powerdown_ctrl.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_bank_timers.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_cmd_arbiter.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_cmd_history_checker.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_dfi_cdc.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_dfi_cmd_path.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_dfi_rd_aligner.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_dfi_wr_serializer.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_page_policy.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_rbl_table.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_rd_cmd_cam.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_rd_intake.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_rd_return_ring.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_row_pred_table.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_wr_data_cam.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_wr_intake.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/pumice_wr_splitter.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/fub/refresh_ctrl.f

# --- Macros ---
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/macro/pumice_axi4_ifc.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/macro/pumice_dfi_layer.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/macro/pumice_mem_cmd_scheduler.f

# --- Tops ---
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/top/pumice_core.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/top/pumice_top.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/top/pumice_top_geared.f
