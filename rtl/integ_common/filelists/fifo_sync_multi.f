# Filelist for fifo_sync_multi
# Location: rtl/integ_common/filelists/fifo_sync_multi.f
#
# Multi-field FIFO wrapper: packs addr/ctrl/data into one fifo_sync.
# An integration example, not a rtl/common library module -- it wires library
# blocks together to show a pattern, which is why it lives in rtl/integ_common
# alongside rtl/integ_amba's examples rather than in the library proper.

+incdir+$REPO_ROOT/rtl/amba/includes

# fifo_sync carries counter_bin and fifo_control itself.
-f $REPO_ROOT/rtl/common/filelists/fifo_sync.f

$REPO_ROOT/rtl/integ_common/fifo_sync_multi.sv
