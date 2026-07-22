# Filelist for axi4_dma_slaves
# Location: rtl/amba/filelists/axi4_dma_slaves.f
#
# Declares the complete compile closure for this component: packages,
# rtl/common dependencies and sub-blocks. Consumers -f include this file
# rather than hand-listing its contents, so internal changes stay internal.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd_pattern_gen.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr_crc_check.f

$REPO_ROOT/rtl/amba/shared/axi4_dma_slaves.sv
