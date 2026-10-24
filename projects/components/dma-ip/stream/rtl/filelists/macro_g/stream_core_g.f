# Filelist for stream_core_g (stream-g, stream TASK-020): the product core on
# scheduler_group_array_g.
# Location: projects/components/dma-ip/stream/rtl/filelists/macro_g/stream_core_g.f
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr_monlite.f
-f $REPO_ROOT/rtl/amba/filelists/axi_bus_meter.f
-f $REPO_ROOT/rtl/amba/filelists/axi_perf_latency_hist.f
$STREAM_ROOT/rtl/includes/stream_pkg.sv
-f $STREAM_ROOT/rtl/filelists/macro_g/scheduler_group_array_g.f
-f $STREAM_ROOT/rtl/filelists/fub/axi_read_engine.f
-f $STREAM_ROOT/rtl/filelists/fub/axi_write_engine.f
-f $STREAM_ROOT/rtl/filelists/fub/sram_controller.f
-f $STREAM_ROOT/rtl/filelists/fub/perf_profiler.f
$STREAM_ROOT/rtl/macro_g/generated/stream_core_g.sv
