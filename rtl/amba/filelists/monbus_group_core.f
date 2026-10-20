# Filelist for monbus_group_core
# Location: rtl/amba/filelists/monbus_group_core.f
#
# Created 2026-10-19 so formal/amba/monbus_group_core builds its flat from this closure
# (make/formal_flat.mk) instead of a hand-listed SRCS.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_cam.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_compressor.f
-f $REPO_ROOT/rtl/math/filelists/math_adder_carry_save_nbit.f
-f $REPO_ROOT/rtl/math/filelists/math_mod_3_compress.f
$REPO_ROOT/rtl/amba/ocelus/monbus_cam_pipe.sv
$REPO_ROOT/rtl/amba/ocelus/monbus_halfbeat_packer.sv
$REPO_ROOT/rtl/amba/ocelus/monbus_group_core.sv
