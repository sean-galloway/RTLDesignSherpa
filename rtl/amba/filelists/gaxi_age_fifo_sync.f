# Filelist for gaxi_age_fifo_sync
# Location: rtl/amba/filelists/gaxi_age_fifo_sync.f
#
# Same compile closure as gaxi_fifo_sync (pointers + control from rtl/common)
# plus the age FIFO itself. Consumers -f include this file.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_age_fifo_sync.sv
