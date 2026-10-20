# Filelist for kestrel_uart_tb_top -- the UART-equivalence sim of build-bram.
# Location: projects/fpga-systems/Genesys2/riscv-ip/kestrel/dv/filelists/kestrel_uart_tb_top.f
# Roots: $REPO_ROOT, $CONVERTERS_ROOT, $KESTREL_ROOT.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $KESTREL_ROOT/rtl/filelists/top/kestrel_core.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_mem_bram.f
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f

$REPO_ROOT/projects/fpga-systems/Genesys2/riscv-ip/kestrel/dv/tb/kestrel_uart_tb_top.sv
