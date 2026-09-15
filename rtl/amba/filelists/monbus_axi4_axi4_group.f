# Filelist for monbus_axi4_axi4_group
# Location: rtl/amba/filelists/monbus_axi4_axi4_group.f
#
# Modelled on monbus_axil4_axi4_group.f, with the AXI4-Lite read slave
# replaced by the full AXI4 one -- this variant instantiates axi4_slave_rd,
# axi4_master_wr and monbus_group_core.
#
# Written 2026-09-15 for TASK-075: this module was the family's one member
# with NO filelist, and TASK-075 records that a missing filelist is what
# leaves a module untestable in the first place ("nothing could build it",
# on apb4_master_cg). Compile order follows the sibling's.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/includes/monitor_arbiter_pkg.sv
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/axi4/axi4_slave_rd.sv
$REPO_ROOT/rtl/amba/axi4/axi4_master_wr.sv
-f $REPO_ROOT/rtl/math/filelists/math_adder_carry_save_nbit.f
-f $REPO_ROOT/rtl/math/filelists/math_mod_3_compress.f
$REPO_ROOT/rtl/amba/monitor/monbus_cam_pipe.sv
$REPO_ROOT/rtl/amba/monitor/monbus_cam.sv
$REPO_ROOT/rtl/amba/monitor/monbus_compressor.sv
# Optional half-beat packer (HALF_BEAT_EN!=0) instantiated inside
# monbus_group_core. Generate-gated, so a default-parameter elaboration
# does not reach it -- it must still be in this component's closure.
$REPO_ROOT/rtl/amba/monitor/monbus_halfbeat_packer.sv
$REPO_ROOT/rtl/amba/monitor/monbus_group_core.sv
$REPO_ROOT/rtl/amba/monitor/monbus_axi4_axi4_group.sv
