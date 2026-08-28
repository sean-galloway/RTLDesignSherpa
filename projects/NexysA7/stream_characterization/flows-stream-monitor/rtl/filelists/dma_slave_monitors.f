# Filelist for dma_slave_monitors (monitored DMA-slave wrapper)
# Composes preexisting component filelists; only the wrapper is new.
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/axi4_dma_slaves.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd_mon.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr_mon.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil4_axil4_group.f
$REPO_ROOT/projects/NexysA7/stream_characterization/flows-stream-monitor/rtl/dma_slave_monitors.sv
