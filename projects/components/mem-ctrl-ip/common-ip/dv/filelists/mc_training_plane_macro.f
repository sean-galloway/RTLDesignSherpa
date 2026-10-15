# Filelist for the mc_training_plane macro test
# (common-ip/dv/tests/macro/test_mc_training_plane.py).
#
# Closure mirrors rtl/filelists/macro/mc_training_plane.f: pkg -> CDC
# primitives -> training shell -> the two LPDDR2 clients -> the plane -> tb.

+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
-f $REPO_ROOT/rtl/cdc/filelists/sync_pulse.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_synchronizer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_training_shell.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_lpddr2_zq_ctrl.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_lpddr2_dq_cal.f
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/macro/mc_training_plane.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/dv/rtl/mc_training_plane_tb_top.sv
