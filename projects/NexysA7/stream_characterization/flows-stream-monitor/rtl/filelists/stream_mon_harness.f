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
-f $STREAM_CHAR_ROOT/rtl/filelists/instrumentation_mon.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil_axil_group.f
# axi4_dma_observer RETIRED 2026-08-14 (superseded by projects/components/misc/rtl/axi4_intf_master_observer.sv).
# This tree is reference-only and no longer elaborates.
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd_mon.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr_mon.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_pkt_tally.f
$STREAM_CHAR_ROOT/rtl/stream_mon_cfg_pkg.sv
$STREAM_CHAR_ROOT/rtl/monbus_tally_axil.sv
$STREAM_CHAR_ROOT/rtl/dma_slave_monitors.sv
$STREAM_CHAR_ROOT/rtl/stream_mon_harness.sv
