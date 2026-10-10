# Filelist for scoria_training_layer
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/rtl/includes/scoria_pkg.sv
# common training shell (pulls in its own CDC primitives)
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_training_layer.f
# rock-side training FUBs
-f $REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_zq_ctrl.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_wrlvl_ifc.f
# this macro
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_training_layer.sv
