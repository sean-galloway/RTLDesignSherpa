# Filelist for axi4_slave_wr_crc_check
# Location: rtl/amba/filelists/axi4_slave_wr_crc_check.f
#
# Declares the complete compile closure for this component: packages,
# rtl/common dependencies and sub-blocks. Consumers -f include this file
# rather than hand-listing its contents, so internal changes stay internal.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc.f

$REPO_ROOT/rtl/amba/shared/axi4_slave_wr_crc_check.sv
