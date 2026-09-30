# Filelist for the latency_bridge DV wrapper (bridge behind a REGISTERED=1 gaxi_fifo_sync)
# Location: projects/components/dma-ip/rapids/dv/filelists/latency_bridge_tb_top.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/fub/latency_bridge.f
$REPO_ROOT/projects/components/dma-ip/rapids/dv/tb/latency_bridge_tb_top.sv
