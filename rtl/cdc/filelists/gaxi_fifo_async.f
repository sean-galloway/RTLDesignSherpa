# Filelist for gaxi_fifo_async
# Location: rtl/cdc/filelists/gaxi_fifo_async.f
#
# Gray/Johnson-pointer asynchronous FIFO and its rtl/common submodules.
# This is the base source set shared by the async buffer tests: the skid
# variant (gaxi_skid_buffer_async) layers its own two files on top of this.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Shared building blocks -- see cdc_fifo_bb.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_fifo_bb.f

$REPO_ROOT/rtl/cdc/gaxi_fifo_async.sv
