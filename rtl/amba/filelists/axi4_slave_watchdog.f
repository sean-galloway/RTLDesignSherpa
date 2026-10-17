# Filelist for axi4_slave_watchdog
# Location: rtl/amba/filelists/axi4_slave_watchdog.f
#
# Declares the complete compile closure for this component. Consumers -f
# include this file rather than hand-listing its contents.

# reset_defs.svh -- this module uses `ALWAYS_FF_RST.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/axi4/axi4_slave_watchdog.sv
