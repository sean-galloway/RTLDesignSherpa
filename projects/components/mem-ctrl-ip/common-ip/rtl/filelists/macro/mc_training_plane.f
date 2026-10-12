# Filelist for mc_training_plane (common-ip training-control macro)
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
# CDC primitives used by the calibration-data crossing
-f $REPO_ROOT/rtl/cdc/filelists/sync_pulse.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_synchronizer.f
# Generic training shell that this macro wraps
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_training_shell.f
# LPDDR2 training clients composed by this macro
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_lpddr2_zq_ctrl.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_lpddr2_dq_cal.f
# the macro
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/macro/mc_training_plane.sv
