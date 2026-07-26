# Filelist for axi4_master_rd_crc_check
# Location: rtl/amba/filelists/axi4_master_rd_crc_check.f

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/reset_defs.svh

-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc_xor_shift.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc_xor_shift_cascade.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc.f
-f $REPO_ROOT/rtl/common/filelists/shifter_lfsr_fibonacci.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_rd.sv
-f $REPO_ROOT/projects/components/misc/rtl/filelists/dma_address_gen.f

$REPO_ROOT/rtl/amba/shared/axi4_master_rd_crc_check.sv
