# Filelist for apb4_master_stub
# Location: rtl/amba/filelists/apb4_master_stub.f
#
# Declares the complete compile closure for this component: packages,
# rtl/common dependencies and sub-blocks. Consumers -f include this file
# rather than hand-listing its contents, so internal changes stay internal.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/apb4_master.f

$REPO_ROOT/rtl/amba/apb4/apb4_master_stub.sv
