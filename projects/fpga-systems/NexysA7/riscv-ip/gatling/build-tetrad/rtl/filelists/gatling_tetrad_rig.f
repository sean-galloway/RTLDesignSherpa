# Filelist for gatling_tetrad_rig -- build-tetrad below the clock: UART ->
# AXI4-Lite -> split -> gatling_mem_bram + gatling_tetrad_harness -> gatling_tetrad.
# Location: projects/fpga-systems/NexysA7/riscv-ip/gatling/build-tetrad/rtl/filelists/gatling_tetrad_rig.f
# Used by the board build (gatling_tetrad_nexysa7_top.f) and the UART-equivalence
# sim (dv/filelists/gatling_tetrad_rig_tb.f), which runs the rig as its toplevel.
# Roots: $REPO_ROOT, $CONVERTERS_ROOT, $GATLING_ROOT (+ $RV32I_COMMON_ROOT via the core).

+incdir+$REPO_ROOT/rtl/amba/includes

# The tetrad (core + Xcell + four cells on alu-infer) and the program memory
-f $GATLING_ROOT/rtl/filelists/top/gatling_tetrad.f
-f $GATLING_ROOT/rtl/filelists/fub/gatling_mem_bram.f

# Host UART front end
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f

# Board-local: the AXIL split, the cell harness, the rig
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f
$REPO_ROOT/projects/fpga-systems/NexysA7/riscv-ip/gatling/rtl/gatling_tetrad_axil_split.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/riscv-ip/gatling/rtl/gatling_tetrad_harness.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/riscv-ip/gatling/rtl/gatling_tetrad_rig.sv
