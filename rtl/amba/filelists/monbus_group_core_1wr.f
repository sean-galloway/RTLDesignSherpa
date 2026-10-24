# Filelist for monbus_group_core_1wr
# Location: rtl/amba/filelists/monbus_group_core_1wr.f
#
# The single-write-port group core (2026-10-23): monbus_group_core's filter
# and trace path, an error path written to its own window, two
# monbus_burst_writer instances merged by monbus_wr_mux2.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_cam.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_compressor.f
$REPO_ROOT/rtl/amba/ocelus/monbus_cam_pipe.sv
$REPO_ROOT/rtl/amba/ocelus/monbus_halfbeat_packer.sv
-f $REPO_ROOT/rtl/amba/filelists/monbus_record_expander.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_burst_writer.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_wr_mux2.f
$REPO_ROOT/rtl/amba/ocelus/monbus_group_core_1wr.sv
