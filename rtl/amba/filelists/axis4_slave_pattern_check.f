# Filelist for axis4_slave_pattern_check
# Location: rtl/amba/filelists/axis4_slave_pattern_check.f
#
# Declares the complete compile closure for this component: packages,
# rtl/common dependencies and sub-blocks. Consumers -f include this file
# rather than hand-listing its contents, so internal changes stay internal.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/common/filelists/dataint_crc.f
-f $REPO_ROOT/rtl/common/filelists/shifter_lfsr_fibonacci.f

$REPO_ROOT/rtl/amba/shared/axis4_slave_pattern_check.sv
