# Filelist for sdpram_core
# Location: rtl/amba/filelists/sdpram_core.f
#
# Declares the complete compile closure for this component: packages,
# rtl/common dependencies and sub-blocks. Consumers -f include this file
# rather than hand-listing its contents, so internal changes stay internal.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/axi_gen_addr.f

$REPO_ROOT/rtl/amba/shared/sdpram_core.sv
