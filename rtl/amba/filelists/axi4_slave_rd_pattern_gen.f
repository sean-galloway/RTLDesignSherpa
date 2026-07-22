# Filelist for axi4_slave_rd_pattern_gen
# Location: rtl/amba/filelists/axi4_slave_rd_pattern_gen.f
#
# Declares the complete compile closure for this component: packages,
# rtl/common dependencies and sub-blocks. Consumers -f include this file
# rather than hand-listing its contents, so internal changes stay internal.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc.f
-f $REPO_ROOT/rtl/common/filelists/shifter_lfsr_fibonacci.f

$REPO_ROOT/rtl/amba/shared/axi4_slave_rd_pattern_gen.sv
