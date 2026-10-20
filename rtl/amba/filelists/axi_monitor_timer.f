# Filelist for axi_monitor_timer
# Location: rtl/amba/filelists/axi_monitor_timer.f
#
# Created 2026-10-19 so formal/amba/axi_monitor_timer builds its flat from this closure
# (make/formal_flat.mk) instead of a hand-listed SRCS.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f
$REPO_ROOT/rtl/amba/ocelus/axi_monitor_timer.sv
