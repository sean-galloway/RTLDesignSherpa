# Filelist for gatling_uart_tb_top -- the UART-equivalence sim of build-bram.
# Location: projects/fpga-systems/NexysA7/riscv-ip/gatling/dv/filelists/gatling_uart_tb_top.f
# Roots: $REPO_ROOT, $CONVERTERS_ROOT, $GATLING_ROOT (+ $KESTREL_ROOT via gatling_core.f).

+incdir+$REPO_ROOT/rtl/amba/includes

-f $GATLING_ROOT/rtl/filelists/top/gatling_core.f
-f $GATLING_ROOT/rtl/filelists/fub/gatling_mem_bram.f
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f

$REPO_ROOT/projects/fpga-systems/NexysA7/riscv-ip/gatling/dv/tb/gatling_uart_tb_top.sv
