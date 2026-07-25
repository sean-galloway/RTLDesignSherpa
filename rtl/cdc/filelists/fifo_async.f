# Filelist for fifo_async module
# Location: rtl/cdc/filelists/fifo_async.f
#
# fifo_async supports BOTH pointer encodings via USE_JOHNSON, and the choice is
# a parameter rather than a separate module, so this filelist must carry the
# dependencies of both paths:
#   USE_JOHNSON=0 (Gray, default) -> counter_bingray + gray2bin
#   USE_JOHNSON=1 (Johnson)       -> counter_bin + counter_johnson + johnson2bin
# The Johnson set is what the retired fifo_async_div2 module used to pull in.

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/rtl/amba/includes/fifo_defs.svh

# Shared dependencies -- owned by rtl/common, reached by -f include.
# These stayed in common on purpose (AMBA-CDC-REORG): they serve FIFOs
# generally, not just clock crossings.
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/glitch_free_n_dff_arn.f
-f $REPO_ROOT/rtl/common/filelists/leading_one_trailing_one.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f

# Gray pointer path (USE_JOHNSON=0)
-f $REPO_ROOT/rtl/cdc/filelists/bin2gray.f
-f $REPO_ROOT/rtl/cdc/filelists/gray2bin.f
-f $REPO_ROOT/rtl/cdc/filelists/counter_bingray.f

# Johnson pointer path (USE_JOHNSON=1)
-f $REPO_ROOT/rtl/cdc/filelists/counter_johnson.f
-f $REPO_ROOT/rtl/cdc/filelists/johnson2bin.f

# fifo_async module
$REPO_ROOT/rtl/cdc/fifo_async.sv
