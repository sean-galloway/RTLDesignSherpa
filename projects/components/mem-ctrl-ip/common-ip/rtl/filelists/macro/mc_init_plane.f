# Filelist for mc_init_plane (common-ip init macro)
# Owns the DRAM bring-up concern: init_sequencer + mode_register shadow.
# Composed by the xDDR2-generation cores (granite product, pumice research)
# with mc_scheduler_plane on its external-init mode (HAS_INIT_SEQUENCER=0,
# HAS_MODE_REGISTER=0).
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
# children
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_xddr2_init_sequencer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_xddr2_mode_register.f
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/macro/mc_init_plane.sv
