# Everything a stream-g top needs below itself (stream TASK-020): the product's
# top_common with stream_core_g, plus the register-mailbox arbiter
# (rapids_g_reg_arb, reused from rapids-g) and the top_g include fragments.
# Location: projects/components/dma-ip/stream/rtl/filelists/top_g/stream_g_top_common.f
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$STREAM_ROOT/rtl/top_g
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave_cdc.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_4_phase_handshake.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_group_1wr.f
$STREAM_ROOT/rtl/includes/stream_pkg.sv
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/peakrdl_to_cmdrsp.f
-f $STREAM_ROOT/rtl/filelists/macro_g/stream_core_g.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_group.f
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro_g/rapids_g_reg_arb.f
$STREAM_ROOT/rtl/top/stream_config_block.sv
