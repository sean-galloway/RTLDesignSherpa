# STREAM top, register-map-independent part (everything but the regblock and the top)
# Location: projects/components/dma-ip/stream/rtl/filelists/top/stream_top_common.f
# Never compiled alone: use stream_top_ch8.f or stream_top_ch16.f, which add their
# regblock and the regsel include dir that picks it.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave_cdc.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_4_phase_handshake.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_axil4_group.f
$STREAM_ROOT/rtl/includes/stream_pkg.sv
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/peakrdl_to_cmdrsp.f
-f $STREAM_ROOT/rtl/filelists/macro/stream_core.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_group.f
$STREAM_ROOT/rtl/top/stream_config_block.sv
