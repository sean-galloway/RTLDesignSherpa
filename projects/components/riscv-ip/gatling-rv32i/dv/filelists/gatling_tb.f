# SPDX-License-Identifier: MIT
# DV filelist for gatling-rv32i: the TB tops on top of the RTL closure.
# RTL sources come in through the blocks' own filelists; only TBs live here.
# The tetrad (Xcell + the cell blocks) has its own TB list,
# gatling_tetrad_tb.f, so these barrel tests do not compile alu-infer.
-f $GATLING_ROOT/rtl/filelists/top/gatling_core.f
-f $GATLING_ROOT/rtl/filelists/fub/gatling_mem_bram.f
$GATLING_ROOT/dv/tb/gatling_tb_top.sv
$GATLING_ROOT/dv/tb/gatling_bram_tb_top.sv
