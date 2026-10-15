# Filelist for axis_bus_meter
# Location: rtl/amba/filelists/axis_bus_meter.f
#
# Declares the complete compile closure for this component: packages,
# rtl/common dependencies and sub-blocks. Consumers -f include this file
# rather than hand-listing its contents, so internal changes stay internal.

+incdir+$REPO_ROOT/rtl/amba/includes

# Boundary reset synchronizer (block input reset is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

$REPO_ROOT/rtl/amba/shared/axis_bus_meter.sv
