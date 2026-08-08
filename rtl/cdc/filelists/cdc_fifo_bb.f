# Building blocks shared by every asynchronous FIFO in this area
# Location: rtl/cdc/filelists/cdc_fifo_bb.f
#
# WHY THIS EXISTS
#   fifo_async, gaxi_fifo_async and the four apb*_slave_cdc* consumers all need
#   the same pointer/control set, and each was repeating it: the same nine -f
#   lines copied six to eight times over. One list, included once each.
#
#   Both pointer encodings are here on purpose. fifo_async and gaxi_fifo_async
#   select between them with USE_JOHNSON at ELABORATION, not at compile time --
#   it is a parameter, not a separate module -- so both paths must be present in
#   the compile closure regardless of how any one instance is configured. That
#   is why this is a single list and not a gray/johnson pair.
#
#   Naming: underscores, matching every other .f in the tree.
#
# WHAT IS NOT HERE
#   The FIFO itself. This list is only the blocks underneath, so a consumer adds
#   its own top after including this.

# Shared control and sync -- owned by rtl/common, reached by -f include.
# leading_one_trailing_one.f carries find_first_set and find_last_set itself.
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/cdc/filelists/glitch_free_n_dff_arn.f
-f $REPO_ROOT/rtl/common/filelists/leading_one_trailing_one.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f

# Gray pointer path (USE_JOHNSON=0).
# bin2gray is deliberately ABSENT: counter_bingray does the binary->Gray
# conversion inline specifically to avoid instantiating it, and nothing else
# here instantiates it either. It was carried in fifo_async.f as dead weight.
# The module is still linted as part of the area via cdc_all.f.
-f $REPO_ROOT/rtl/cdc/filelists/gray2bin.f
-f $REPO_ROOT/rtl/cdc/filelists/counter_bingray.f

# Johnson pointer path (USE_JOHNSON=1)
-f $REPO_ROOT/rtl/cdc/filelists/counter_johnson.f
-f $REPO_ROOT/rtl/cdc/filelists/johnson2bin.f
