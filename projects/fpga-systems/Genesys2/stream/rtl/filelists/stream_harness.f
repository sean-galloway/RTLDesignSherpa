+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$STREAM_ROOT/regs/generated/rtl
-f $STREAM_ROOT/rtl/filelists/top/stream_top_ch8.f
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc_xor_shift.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc_xor_shift_cascade.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc.f
-f $REPO_ROOT/rtl/common/filelists/shifter_lfsr_fibonacci.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd_pattern_gen.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr_crc_check.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_dma_slaves.f
-f $FRAMEWORK_ROOT/rtl/filelists/instrumentation_mon.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil_axil_group.f
-f $MISC_ROOT/rtl/filelists/axi4_intf_observer.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd_mon.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr_mon.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_pkt_tally.f
$FRAMEWORK_ROOT/rtl/stream_cfg_pkg.sv
$FRAMEWORK_ROOT/rtl/monbus_tally_axil.sv
# dma_slave_monitors owns its own compile closure (regblock + APB chain) in
# misc/ -- a consumer -f includes it rather than hand-listing its sources.
-f $MISC_ROOT/rtl/filelists/dma_slave_monitors.f
$FRAMEWORK_ROOT/rtl/stream_harness.sv
