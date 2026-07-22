# Filelist for axi4_slave_stub
# Location: rtl/amba/filelists/axi4_slave_stub.f
#
# Declares the complete compile closure for this component: packages,
# rtl/common dependencies and sub-blocks. Consumers -f include this file
# rather than hand-listing its contents, so internal changes stay internal.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd_stub.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr_stub.f

$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_stub.sv
