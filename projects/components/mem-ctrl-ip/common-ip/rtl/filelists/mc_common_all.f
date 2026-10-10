# ==============================================================================
# mc_all - master filelist for the mem-ctrl family common layers
# ==============================================================================
#
# Purpose: the compile closure for everything common-ip owns. Research
#          controllers (research-ip/<rock>/) -f the per-block lists (or this
#          master) as they adopt each layer in the Phase 2 extraction
#          (docs/superpowers/plans/2026-10-10-mem-ctrl-ip-phase2-common-extraction.md).
# Usage:   verilator --lint-only -f filelists/mc_all.f
#
# Written 2026-10-10 with the package (Task 1); per-layer lists join as the
# extraction lands (Tasks 2-6).

# --- Family package (must compile first) ---
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_addr_mapper.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_axi_burst_chopper.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_timer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_timers.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_global_timers.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_rd_cmd_cam.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_rd_intake.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_wr_data_cam.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_wr_intake.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_wr_splitter.f
