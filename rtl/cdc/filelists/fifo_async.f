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

# Shared building blocks -- one list, both pointer encodings.
# See cdc_fifo_bb.f for why both paths are always present.
-f $REPO_ROOT/rtl/cdc/filelists/cdc_fifo_bb.f

# fifo_async module
$REPO_ROOT/rtl/cdc/fifo_async.sv
