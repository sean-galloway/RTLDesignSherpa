# Filelist for axi_monitor_trans_mgr
# Location: rtl/amba/filelists/axi_monitor_trans_mgr.f
#
# Created 2026-10-19 so formal/amba/axi_monitor_trans_mgr and formal/amba/axi_monitor_trans_mgr_banked builds its flat from this closure
# (make/formal_flat.mk) instead of a hand-listed SRCS.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
-f $REPO_ROOT/rtl/amba/filelists/monitor_trans_cam.f
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_trans_mgr.sv
