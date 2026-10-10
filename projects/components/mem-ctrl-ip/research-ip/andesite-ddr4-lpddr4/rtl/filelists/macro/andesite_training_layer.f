# Filelist for andesite_training_layer
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/includes/andesite_pkg.sv
# common training shell (pulls in its own CDC primitives)
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_training_layer.f
# The three training FUBs this layer owns
-f $REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/filelists/fub/andesite_wrlvl_ifc.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/filelists/fub/andesite_rdlvl_ifc.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/filelists/fub/andesite_ca_train_ifc.f
# This macro
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/macro/andesite_training_layer.sv
