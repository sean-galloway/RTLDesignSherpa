# Filelist for cell_mem_in -- the cell's input operand memory.
# Location: projects/components/compute-eng-ip/cell/rtl/filelists/cell_mem_in.f
#
# Its own closure: the reset macros and cell_pkg (COORD_BITS).  cell_top.f
# includes this file; so does riscv-ip/gatling-rv32i's gatling_tetrad.f,
# whose Xcell unit drives the read port.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

$REPO_ROOT/projects/components/compute-eng-ip/cell/rtl/cell_pkg.sv
$REPO_ROOT/projects/components/compute-eng-ip/cell/rtl/cell_mem_in.sv
