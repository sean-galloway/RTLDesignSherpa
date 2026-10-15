# Filelist for the mc_init_plane macro test
# (common-ip/dv/tests/macro/test_mc_init_plane.py).
#
# Closure: reset_defs + family pkg -> the plane under test (+ children) ->
# tb top.

+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_xddr2_init_sequencer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_xddr2_mode_register.f
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/macro/mc_init_plane.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/dv/rtl/mc_init_plane_tb_top.sv
