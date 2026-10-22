# Filelist for mc_storage_plane (common-ip; extracted from mc_axi4_plane Phase 2 stack)
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
# CAMs owned by this plane
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_wr_data_cam.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_rd_cmd_cam.f
# per-bank head records (the storage -> scheduler contract), derived from the CAMs
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_head_records.f
# wrapper
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/macro/mc_storage_plane.sv
