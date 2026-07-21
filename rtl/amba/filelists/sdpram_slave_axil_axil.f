# Filelist for sdpram_slave_axil_axil
# Location: rtl/amba/filelists/sdpram_slave_axil_axil.f
#
# Declares the complete compile closure for this component: packages,
# rtl/common dependencies and sub-blocks. Consumers -f include this file
# rather than hand-listing its contents, so internal changes stay internal.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_core.f

$REPO_ROOT/rtl/amba/shared/sdpram_slave_axil_axil.sv
