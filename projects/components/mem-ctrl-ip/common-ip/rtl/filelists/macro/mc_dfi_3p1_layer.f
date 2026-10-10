# Filelist for mc_dfi_3p1_layer (common-ip DFI 3.1 macro)
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
# DFI datapath fubs
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_dfi_cdc.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_dfi_3p1_cmd_path.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_dfi_wr_serializer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_dfi_rd_aligner.f
# write-leveling CDC primitives (DDR3 per-CS leveling handshake)
-f $REPO_ROOT/rtl/cdc/filelists/cdc_synchronizer.f
-f $REPO_ROOT/rtl/cdc/filelists/sync_pulse.f
# this macro
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/macro/mc_dfi_3p1_layer.sv
