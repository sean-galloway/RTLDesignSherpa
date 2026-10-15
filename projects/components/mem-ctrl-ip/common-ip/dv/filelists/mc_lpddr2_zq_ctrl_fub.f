# Filelist for the mc_lpddr2_zq_ctrl fub policy test
# (common-ip/dv/tests/fub/test_mc_lpddr2_zq_ctrl.py).
#
# Closure: pkg -> the ZQ controller under test -> tb top.

+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_lpddr2_zq_ctrl.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/dv/rtl/mc_lpddr2_zq_ctrl_tb_top.sv
