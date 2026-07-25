# Filelist for gaxi_skid_buffer_async
# Location: rtl/cdc/filelists/gaxi_skid_buffer_async.f
#
# The skid-buffered asynchronous FIFO: gaxi_fifo_async with a gaxi_skid_buffer
# on each side. It layers exactly two files on the async base, so this list is
# the base filelist plus those two -- it does NOT restate the base's sources.
#
# Before this existed, val/amba/test_gaxi_buffer_async.py included
# gaxi_fifo_async.f and then hand-appended the two skid sources. That is the
# hand-listing the filelist rule forbids: the appended paths rot silently the
# moment this area moves a file, which is exactly what the rtl/cdc move did.

-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f

$REPO_ROOT/rtl/cdc/gaxi_skid_buffer_async.sv
