# Filelist for mc_ocelus_plane (common-ip): the controller's Ocelus plane --
# two axi_monitor_lite port taps, mc_monlite on internal events, a 3-client
# monbus_arbiter and the write-only monbus_axil4_group_1wr.
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
-f $REPO_ROOT/rtl/amba/filelists/axi_monitor_lite.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_group_1wr.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_monlite.f
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/macro/mc_ocelus_plane.sv
