# Filelist for axi4_wr_aggregator
# Location: rtl/amba/filelists/axi4_wr_aggregator.f

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
-f $REPO_ROOT/rtl/amba/filelists/axi4_aggregator_cmd.f

$REPO_ROOT/rtl/amba/shared/axi4_wr_aggregator.sv
