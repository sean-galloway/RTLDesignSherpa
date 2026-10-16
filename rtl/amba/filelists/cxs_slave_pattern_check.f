# Filelist for cxs_slave_pattern_check
# Location: rtl/amba/filelists/cxs_slave_pattern_check.f
#
# Complete compile closure: the AXIS block it wraps, the AXIS<->CXS adapter
# and the CXS endpoint, each through its own filelist.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/axis4_slave_pattern_check.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/cxs_to_axis.f
-f $REPO_ROOT/rtl/amba/filelists/cxs_slave.f

$REPO_ROOT/rtl/amba/shared/cxs_slave_pattern_check.sv
