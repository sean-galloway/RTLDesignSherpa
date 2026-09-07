# Filelist for axi4_subtractive_slave
# Location: rtl/amba/filelists/axi4_subtractive_slave.f
#
# Declares the complete compile closure for this component: packages,
# rtl/common dependencies and sub-blocks. Consumers -f include this file
# rather than hand-listing its contents, so internal changes stay internal.

# reset_defs.svh -- this module uses `ALWAYS_FF_RST, so its macro header
# must be on the include path and compiled before it.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# monitor packages -- create_monitor_packet, PktTypeError, AXI_ERR_ADDR_RANGE
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/axi4/axi4_subtractive_slave.sv
