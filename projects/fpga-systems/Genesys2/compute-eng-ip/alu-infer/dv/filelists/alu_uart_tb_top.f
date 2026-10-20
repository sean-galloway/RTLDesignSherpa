# Filelist for alu_uart_tb_top -- the UART-equivalence sim of build-infer.
# Location: projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/dv/filelists/alu_uart_tb_top.f
#
# The board build's closure minus the board top (no MMCM/IBUFDS), plus the
# sim top. Roots: $REPO_ROOT, $CONVERTERS_ROOT.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/filelists/alu_infer_top.f
$REPO_ROOT/projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/build-infer/rtl/alu_slot.sv
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f
-f $REPO_ROOT/projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/rtl/filelists/alu_harness.f

$REPO_ROOT/projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/dv/tb/alu_uart_tb_top.sv
