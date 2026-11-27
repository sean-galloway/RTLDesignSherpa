# Filelist for gatling_tetrad (top) -- gatling sequencing its tetrad's cells:
# gatling_core with Xcell, the Xcell unit, and per context the cell's input
# memory, alu-infer ALU and result memory.
# Location: projects/components/riscv-ip/gatling-rv32i/rtl/filelists/top/gatling_tetrad.f
#
# The cell blocks belong to compute-eng-ip (cell, alu-infer) and come in
# through their own filelists; this file never hand-lists them.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

-f $GATLING_ROOT/rtl/filelists/top/gatling_core.f
-f $GATLING_ROOT/rtl/filelists/fub/gatling_xcell.f

-f $REPO_ROOT/projects/components/compute-eng-ip/cell/rtl/filelists/cell_mem_in.f
-f $REPO_ROOT/projects/components/compute-eng-ip/cell/rtl/filelists/cell_mem_out.f
-f $REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/filelists/alu_infer_top.f

$GATLING_ROOT/rtl/top/gatling_tetrad.sv
