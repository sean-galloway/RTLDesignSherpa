# Filelist for cxs_master_injector
# Location: rtl/amba/filelists/cxs_master_injector.f
#
# Complete compile closure: the AXIS block it wraps, the AXIS<->CXS adapter
# and the CXS endpoint, each through its own filelist.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/axis4_master_injector.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axis_to_cxs.f
-f $REPO_ROOT/rtl/amba/filelists/cxs_master.f

$REPO_ROOT/rtl/amba/shared/cxs_master_injector.sv
