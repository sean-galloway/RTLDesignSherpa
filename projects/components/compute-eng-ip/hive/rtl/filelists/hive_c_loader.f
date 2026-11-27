# Filelist for hive_c_loader
# Location: projects/components/compute-eng-ip/hive/rtl/filelists/hive_c_loader.f
#
# HIVE-C core + two 32 KB banks + the AXIL load-then-run window (Block 1).
# Core glue per CORE_FLAVOR: vexriscv below; peregrine's glue joins this
# list when it is built (riscv-ip/peregrine-rv32im TASK-004).

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f
-f $REPO_ROOT/projects/components/compute-eng-ip/hive/rtl/filelists/hive_c_bram.f
-f $REPO_ROOT/projects/components/compute-eng-ip/hive/rtl/filelists/hive_c_core_vexriscv.f

$REPO_ROOT/projects/components/compute-eng-ip/hive/rtl/hive_c_controller/hive_c_loader.sv
