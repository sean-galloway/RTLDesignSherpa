# Filelist for cell_mem_out -- the cell's result memory.
# Location: projects/components/compute-eng-ip/cell/rtl/filelists/cell_mem_out.f
#
# Its own closure: the reset macros.  cell_top.f includes this file; so does
# riscv-ip/gatling-rv32i's gatling_tetrad.f, whose Xcell unit drives the
# write port.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

$REPO_ROOT/projects/components/compute-eng-ip/cell/rtl/cell_mem_out.sv
