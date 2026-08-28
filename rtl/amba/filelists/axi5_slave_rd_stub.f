# Filelist for axi5_slave_rd_stub
# Location: rtl/amba/filelists/axi5_slave_rd_stub.f
#
# Declares the complete compile closure for this component: packages,
# rtl/common dependencies and sub-blocks. Consumers -f include this file
# rather than hand-listing its contents, so internal changes stay internal.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/axi5/stubs/axi5_slave_rd_stub.sv
